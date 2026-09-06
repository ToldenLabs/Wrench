import re
import sys
import time
import ipaddress
from collections import OrderedDict, deque
from urllib.parse import urljoin, urlparse, urldefrag

import httpx
import html5lib


APP_NAME = "Wrench"
VERSION = "1.0"

# ============================================================
# HARD LIMITS
# ============================================================

MAX_RESPONSE_SIZE = 15 * 1024 * 1024
MAX_RENDERED_CHARS = 2_000_000
MAX_HISTORY = 100
MAX_LINKS = 2000
MAX_CACHE_ENTRIES = 16
MAX_REDIRECTS = 10

# ============================================================
# RATE LIMITS / COOLDOWNS
# ============================================================

# 1. Global request cooldown.
GLOBAL_REQUEST_COOLDOWN = 0.20

# 2. Minimum delay between requests to the same host.
HOST_REQUEST_COOLDOWN = 0.50

# 3. Rolling global burst limit.
GLOBAL_BURST_WINDOW = 10.0
GLOBAL_BURST_MAX = 20

# 4. Rolling per-host burst limit.
HOST_BURST_WINDOW = 10.0
HOST_BURST_MAX = 8

# 5. Rendering cooldown.
RENDER_COOLDOWN = 0.10

# 6. Link-opening cooldown.
LINK_COOLDOWN = 0.25

# 7. Command burst protection.
COMMAND_BURST_WINDOW = 5.0
COMMAND_BURST_MAX = 40

# 8. History-operation cooldown.
HISTORY_COOLDOWN = 0.05

# ============================================================
# NETWORK
# ============================================================

CONNECT_TIMEOUT = 8.0
READ_TIMEOUT = 12.0
WRITE_TIMEOUT = 8.0
POOL_TIMEOUT = 5.0

SAFE_SCHEMES = frozenset({
    "http",
    "https",
})

# ============================================================
# HTML
# ============================================================

IGNORED_TAGS = frozenset({
    "script",
    "style",
    "noscript",
    "template",
    "svg",
    "canvas",
    "math",
    "head",
    "meta",
    "link",
    "iframe",
    "object",
    "embed",
    "video",
    "audio",
    "source",
    "track",
    "picture",
})

BLOCK_TAGS = frozenset({
    "address",
    "article",
    "aside",
    "blockquote",
    "dd",
    "details",
    "dialog",
    "div",
    "dl",
    "dt",
    "fieldset",
    "figcaption",
    "figure",
    "footer",
    "form",
    "header",
    "main",
    "nav",
    "ol",
    "p",
    "pre",
    "section",
    "summary",
    "table",
    "tbody",
    "td",
    "tfoot",
    "th",
    "thead",
    "tr",
    "ul",
})

HEADING_LEVELS = {
    "h1": 1,
    "h2": 2,
    "h3": 3,
    "h4": 4,
    "h5": 5,
    "h6": 6,
}

WHITESPACE_RE = re.compile(r"\s+")

ANSI_RE = re.compile(
    r"""
    \x1B
    (?:
        \[[0-?]*[ -/]*[@-~]
        |
        \][^\x07]*(?:\x07|\x1B\\)
        |
        [()][0-2A-Z]
        |
        [@-_]
    )
    """,
    re.VERBOSE,
)

CONTROL_RE = re.compile(
    r"[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]"
)


class Wrench:
    __slots__ = (
        "client",
        "parser",
        "history",
        "history_index",
        "links",
        "current_url",
        "current_title",
        "cache",
        "rendered_chars",

        # Rate limiting.
        "last_request_time",
        "last_render_time",
        "last_link_time",
        "last_history_time",
        "host_last_request",
        "global_requests",
        "host_requests",
        "command_times",
    )

    def __init__(self):
        timeout = httpx.Timeout(
            timeout=READ_TIMEOUT,
            connect=CONNECT_TIMEOUT,
            read=READ_TIMEOUT,
            write=WRITE_TIMEOUT,
            pool=POOL_TIMEOUT,
        )

        limits = httpx.Limits(
            max_connections=8,
            max_keepalive_connections=4,
            keepalive_expiry=30.0,
        )

        self.client = httpx.Client(
            follow_redirects=True,
            max_redirects=MAX_REDIRECTS,
            verify=True,
            timeout=timeout,
            limits=limits,
            http2=False,
            headers={
                "User-Agent": (
                    "Wrench/3.1 "
                    "(HTML-only terminal browser)"
                ),
                "Accept": (
                    "text/html,"
                    "application/xhtml+xml"
                ),
                "Accept-Encoding": (
                    "gzip, deflate, br"
                ),
                "Cache-Control": "no-cache",
                "Pragma": "no-cache",
            },
        )

        # Standards-compliant HTML5 parser.
        self.parser = html5lib.HTMLParser(
            namespaceHTMLElements=False,
            strict=False,
        )

        self.history = []
        self.history_index = -1

        self.links = []
        self.current_url = None
        self.current_title = ""

        # Only HTML bytes are cached.
        self.cache = OrderedDict()

        self.rendered_chars = 0

        # ====================================================
        # RATE-LIMIT STATE
        # ====================================================

        self.last_request_time = 0.0
        self.last_render_time = 0.0
        self.last_link_time = 0.0
        self.last_history_time = 0.0

        self.host_last_request = {}

        self.global_requests = deque()
        self.host_requests = {}

        self.command_times = deque()

    # ========================================================
    # RATE LIMITING
    # ========================================================

    @staticmethod
    def wait_for_cooldown(
        last_time,
        cooldown,
    ):
        now = time.monotonic()

        remaining = (
            cooldown
            - (now - last_time)
        )

        if remaining > 0:
            time.sleep(remaining)

        return time.monotonic()

    def cleanup_times(
        self,
        queue,
        now,
        window,
    ):
        cutoff = now - window

        while queue and queue[0] <= cutoff:
            queue.popleft()

    def allow_command(self):
        now = time.monotonic()

        self.cleanup_times(
            self.command_times,
            now,
            COMMAND_BURST_WINDOW,
        )

        if (
            len(self.command_times)
            >= COMMAND_BURST_MAX
        ):
            print(
                "\nCommand rate limit reached. "
                "Slow down for a moment.\n"
            )
            return False

        self.command_times.append(now)
        return True

    def request_allowed(self, host):
        now = time.monotonic()

        # ----------------------------------------------------
        # Global cooldown.
        # ----------------------------------------------------

        now = self.wait_for_cooldown(
            self.last_request_time,
            GLOBAL_REQUEST_COOLDOWN,
        )

        self.last_request_time = now

        # ----------------------------------------------------
        # Per-host cooldown.
        # ----------------------------------------------------

        previous = self.host_last_request.get(
            host,
            0.0,
        )

        now = self.wait_for_cooldown(
            previous,
            HOST_REQUEST_COOLDOWN,
        )

        self.host_last_request[host] = now

        # ----------------------------------------------------
        # Global rolling burst.
        # ----------------------------------------------------

        self.cleanup_times(
            self.global_requests,
            now,
            GLOBAL_BURST_WINDOW,
        )

        if (
            len(self.global_requests)
            >= GLOBAL_BURST_MAX
        ):
            wait = (
                self.global_requests[0]
                + GLOBAL_BURST_WINDOW
                - now
            )

            if wait > 0:
                time.sleep(wait)

            now = time.monotonic()

            self.cleanup_times(
                self.global_requests,
                now,
                GLOBAL_BURST_WINDOW,
            )

        self.global_requests.append(now)

        # ----------------------------------------------------
        # Per-host rolling burst.
        # ----------------------------------------------------

        queue = self.host_requests.get(host)

        if queue is None:
            queue = deque()
            self.host_requests[host] = queue

        self.cleanup_times(
            queue,
            now,
            HOST_BURST_WINDOW,
        )

        if len(queue) >= HOST_BURST_MAX:
            wait = (
                queue[0]
                + HOST_BURST_WINDOW
                - now
            )

            if wait > 0:
                time.sleep(wait)

            now = time.monotonic()

            self.cleanup_times(
                queue,
                now,
                HOST_BURST_WINDOW,
            )

        queue.append(now)

        return True

    def render_allowed(self):
        now = time.monotonic()

        now = self.wait_for_cooldown(
            self.last_render_time,
            RENDER_COOLDOWN,
        )

        self.last_render_time = now

    def link_allowed(self):
        now = time.monotonic()

        remaining = (
            LINK_COOLDOWN
            - (now - self.last_link_time)
        )

        if remaining > 0:
            print(
                "\nLink cooldown active. "
                "Please wait a moment.\n"
            )
            return False

        self.last_link_time = now
        return True

    def history_allowed(self):
        now = time.monotonic()

        remaining = (
            HISTORY_COOLDOWN
            - (now - self.last_history_time)
        )

        if remaining > 0:
            return False

        self.last_history_time = now
        return True

    # ========================================================
    # TERMINAL SECURITY
    # ========================================================

    @staticmethod
    def terminal_safe(text):
        if not text:
            return ""

        text = ANSI_RE.sub(
            "",
            text,
        )

        text = CONTROL_RE.sub(
            "",
            text,
        )

        return text

    @classmethod
    def clean_text(cls, text):
        if not text:
            return ""

        text = cls.terminal_safe(text)

        if not text:
            return ""

        return WHITESPACE_RE.sub(
            " ",
            text.replace(
                "\xa0",
                " ",
            ),
        ).strip()

    # ========================================================
    # URL SECURITY
    # ========================================================

    @staticmethod
    def normalize_url(value):
        if not value:
            return None

        value = value.strip()

        if not value:
            return None

        # Reject control characters before parsing.
        for char in value:
            if ord(char) < 32:
                return None

        parsed = urlparse(value)

        if not parsed.scheme:
            value = "https://" + value
            parsed = urlparse(value)

        scheme = parsed.scheme.lower()

        if scheme not in SAFE_SCHEMES:
            return None

        if not parsed.netloc:
            return None

        # Never accept embedded username/password.
        if parsed.username is not None:
            return None

        if parsed.password is not None:
            return None

        value, _ = urldefrag(value)

        return value

    @staticmethod
    def host_is_private(host):
        if not host:
            return True

        host = host.strip().lower().rstrip(".")

        if (
            host == "localhost"
            or host.endswith(".localhost")
            or host.endswith(".local")
            or host.endswith(".internal")
        ):
            return True

        try:
            address = ipaddress.ip_address(
                host.strip("[]")
            )

            return (
                address.is_private
                or address.is_loopback
                or address.is_link_local
                or address.is_multicast
                or address.is_reserved
                or address.is_unspecified
            )

        except ValueError:
            pass

        return False

    @classmethod
    def validate_network_url(cls, url):
        parsed = urlparse(url)

        if parsed.scheme.lower() not in SAFE_SCHEMES:
            return False

        if not parsed.hostname:
            return False

        if cls.host_is_private(
            parsed.hostname
        ):
            return False

        return True

    # ========================================================
    # CACHE
    # ========================================================

    def cache_get(self, url):
        data = self.cache.get(url)

        if data is None:
            return None

        self.cache.move_to_end(url)

        return data

    def cache_put(self, url, data):
        self.cache[url] = data
        self.cache.move_to_end(url)

        if len(self.cache) > MAX_CACHE_ENTRIES:
            self.cache.popitem(last=False)

    # ========================================================
    # PRIVACY
    # ========================================================

    def clear_privacy_state(self):
        try:
            self.client.cookies.clear()
        except Exception:
            pass

    # ========================================================
    # NETWORK
    # ========================================================

    def fetch(self, url, use_cache=True):
        if not self.validate_network_url(url):
            print(
                "\nBlocked unsafe/local network URL.\n"
            )
            return None, None

        if use_cache:
            cached = self.cache_get(url)

            if cached is not None:
                return url, cached

        parsed = urlparse(url)
        host = parsed.hostname

        if not host:
            return None, None

        self.request_allowed(host)

        try:
            with self.client.stream(
                "GET",
                url,
                headers={
                    # Do not leak navigation history.
                    "Referer": "",
                },
            ) as response:

                response.raise_for_status()

                content_type = response.headers.get(
                    "content-type",
                    "",
                ).lower()

                # HTML only.
                if (
                    "text/html" not in content_type
                    and
                    "application/xhtml+xml"
                    not in content_type
                ):
                    print(
                        "\nWrench only renders HTML.\n"
                        f"Content-Type: "
                        f"{content_type or 'unknown'}\n"
                    )

                    return None, None

                length = response.headers.get(
                    "content-length"
                )

                if length:
                    try:
                        if int(length) > MAX_RESPONSE_SIZE:
                            print(
                                "\nPage exceeds Wrench's "
                                "size limit.\n"
                            )
                            return None, None

                    except ValueError:
                        pass

                chunks = []
                total = 0
                append = chunks.append

                for chunk in response.iter_bytes(
                    chunk_size=64 * 1024
                ):
                    total += len(chunk)

                    if total > MAX_RESPONSE_SIZE:
                        print(
                            "\nPage exceeds Wrench's "
                            "size limit.\n"
                        )
                        return None, None

                    append(chunk)

                html = b"".join(chunks)

                final_url = self.normalize_url(
                    str(response.url)
                )

                if not final_url:
                    return None, None

                if not self.validate_network_url(
                    final_url
                ):
                    print(
                        "\nBlocked redirect to an "
                        "unsafe/local network URL.\n"
                    )
                    return None, None

                self.cache_put(
                    final_url,
                    html,
                )

                return final_url, html

        except httpx.HTTPStatusError as error:
            print(
                f"\nHTTP {error.response.status_code}: "
                f"{error.response.reason_phrase}\n"
            )

        except httpx.TooManyRedirects:
            print(
                "\nToo many redirects.\n"
            )

        except httpx.TimeoutException:
            print(
                "\nRequest timed out.\n"
            )

        except httpx.ConnectError:
            print(
                "\nConnection failed.\n"
            )

        except httpx.RequestError as error:
            print(
                f"\nNetwork error: {error}\n"
            )

        finally:
            self.clear_privacy_state()

        return None, None

    # ========================================================
    # HTML HELPERS
    # ========================================================

    @staticmethod
    def tag_name(element):
        tag = element.tag

        if not isinstance(tag, str):
            return ""

        if "}" in tag:
            tag = tag.rsplit(
                "}",
                1,
            )[1]

        return tag.lower()

    @classmethod
    def subtree_text(cls, element):
        parts = []
        append = parts.append

        if element.text:
            append(element.text)

        stack = list(
            reversed(element)
        )

        while stack:
            node = stack.pop()

            if node.text:
                append(node.text)

            if node.tail:
                append(node.tail)

            for child in reversed(node):
                stack.append(child)

        return "".join(parts)

    # ========================================================
    # DOCUMENT PARTS
    # ========================================================

    def find_document_parts(self, document):
        body = None
        title = ""

        stack = [document]

        while stack:
            element = stack.pop()

            tag = self.tag_name(element)

            if tag == "title" and not title:
                title = self.clean_text(
                    self.subtree_text(element)
                )

            elif tag == "body":
                body = element
                break

            for child in reversed(element):
                stack.append(child)

        return body, title

    # ========================================================
    # RENDER
    # ========================================================

    def render(self, html, base_url):
        self.render_allowed()

        self.links.clear()
        self.current_title = ""
        self.rendered_chars = 0

        try:
            document = self.parser.parse(html)

        except Exception as error:
            print(
                f"\nHTML parsing error: {error}\n"
            )
            return

        body, title = self.find_document_parts(
            document
        )

        self.current_title = title

        if title:
            print("\n" + "=" * 72)
            print(title)
            print("=" * 72)

        if body is None:
            body = document

        output = []
        current = []

        append_output = output.append
        append_current = current.append
        links = self.links

        def flush():
            if not current:
                return

            text = self.clean_text(
                " ".join(current)
            )

            current.clear()

            if not text:
                return

            if (
                self.rendered_chars
                >= MAX_RENDERED_CHARS
            ):
                return

            self.rendered_chars += len(text)

            append_output(text)

        def add_text(text):
            if not text:
                return

            if (
                self.rendered_chars
                >= MAX_RENDERED_CHARS
            ):
                return

            cleaned = self.clean_text(text)

            if cleaned:
                append_current(cleaned)

        def walk(element):
            if (
                self.rendered_chars
                >= MAX_RENDERED_CHARS
            ):
                return

            tag = self.tag_name(element)

            if tag in IGNORED_TAGS:
                return

            # Heading.
            level = HEADING_LEVELS.get(tag)

            if level is not None:
                flush()

                text = self.clean_text(
                    self.subtree_text(element)
                )

                if text:
                    self.rendered_chars += len(text)

                    if (
                        self.rendered_chars
                        <= MAX_RENDERED_CHARS
                    ):
                        append_output(
                            ("#" * level)
                            + " "
                            + text
                        )

                return

            # Link.
            if tag == "a":
                text = self.clean_text(
                    self.subtree_text(element)
                )

                if not text:
                    return

                href = element.attrib.get(
                    "href"
                )

                if not href:
                    add_text(text)
                    return

                absolute = urljoin(
                    base_url,
                    href,
                )

                absolute = self.normalize_url(
                    absolute
                )

                if (
                    absolute
                    and
                    self.validate_network_url(
                        absolute
                    )
                    and
                    len(links) < MAX_LINKS
                ):
                    links.append(
                        (
                            text,
                            absolute,
                        )
                    )

                    add_text(
                        f"[{len(links)}] {text}"
                    )

                else:
                    add_text(text)

                return

            # Never download images.
            if tag == "img":
                alt = self.clean_text(
                    element.attrib.get(
                        "alt",
                        "",
                    )
                )

                add_text(
                    (
                        f"[Image: {alt}]"
                        if alt
                        else "[Image]"
                    )
                )

                return

            if tag == "br":
                flush()
                return

            if tag == "hr":
                flush()
                append_output("-" * 72)
                return

            # List item.
            if tag == "li":
                flush()

                if element.text:
                    add_text(
                        element.text
                    )

                for child in element:
                    walk(child)

                    if child.tail:
                        add_text(
                            child.tail
                        )

                flush()

                if output:
                    output[-1] = (
                        "• "
                        + output[-1]
                    )

                return

            is_block = tag in BLOCK_TAGS

            if is_block:
                flush()

            if element.text:
                add_text(
                    element.text
                )

            for child in element:
                walk(child)

                if child.tail:
                    add_text(
                        child.tail
                    )

            if is_block:
                flush()

        walk(body)
        flush()

        # ====================================================
        # Final output cleanup.
        # ====================================================

        cleaned_output = []
        previous_blank = False

        append_cleaned = cleaned_output.append

        for line in output:
            line = self.terminal_safe(
                line
            ).strip()

            if not line:
                if not previous_blank:
                    append_cleaned("")

                previous_blank = True
                continue

            append_cleaned(line)
            previous_blank = False

        print()

        if cleaned_output:
            sys.stdout.write(
                "\n".join(
                    cleaned_output
                )
            )
            sys.stdout.write("\n")

        else:
            print(
                "[No readable HTML content found.]"
            )

        # ====================================================
        # Links.
        # ====================================================

        if links:
            chunks = [
                "",
                "=" * 72,
                "LINKS",
                "=" * 72,
            ]

            append = chunks.append

            for index, (text, url) in enumerate(
                links,
                1,
            ):
                append(
                    f"[{index}] {text}"
                )
                append(
                    f"     {url}"
                )

            sys.stdout.write(
                "\n".join(chunks)
            )
            sys.stdout.write("\n")

    # ========================================================
    # HISTORY
    # ========================================================

    def add_history(self, url):
        if (
            self.history_index >= 0
            and self.history[
                self.history_index
            ] == url
        ):
            return

        if (
            self.history_index
            < len(self.history) - 1
        ):
            del self.history[
                self.history_index + 1:
            ]

        self.history.append(url)

        if len(self.history) > MAX_HISTORY:
            del self.history[0]

        self.history_index = (
            len(self.history) - 1
        )

    def back(self):
        if not self.history_allowed():
            return

        if self.history_index <= 0:
            print(
                "\nNo previous page.\n"
            )
            return

        self.history_index -= 1

        self.load(
            self.history[
                self.history_index
            ],
            add_history=False,
        )

    def forward(self):
        if not self.history_allowed():
            return

        if (
            self.history_index < 0
            or self.history_index
            >= len(self.history) - 1
        ):
            print(
                "\nNo next page.\n"
            )
            return

        self.history_index += 1

        self.load(
            self.history[
                self.history_index
            ],
            add_history=False,
        )

    # ========================================================
    # LOAD
    # ========================================================

    def load(self, value, add_history=True):
        url = self.normalize_url(value)

        if not url:
            print(
                "\nInvalid or unsupported URL.\n"
            )
            return

        if not self.validate_network_url(url):
            print(
                "\nBlocked unsafe/local network URL.\n"
            )
            return

        cached = self.cache_get(url)

        if cached is not None:
            final_url = url
            html = cached

            print(
                f"\nLoading {url}... (cached)"
            )

        else:
            print(
                f"\nLoading {url}..."
            )

            final_url, html = self.fetch(
                url,
                use_cache=False,
            )

            if final_url is None:
                return

        if add_history:
            self.add_history(
                final_url
            )

        self.current_url = final_url

        print("\n" + "=" * 72)
        print(
            f"{APP_NAME} {VERSION}"
        )
        print(
            f"URL: {final_url}"
        )
        print("=" * 72)

        self.render(
            html,
            final_url,
        )

    # ========================================================
    # LINKS
    # ========================================================

    def open_link(self, value):
        if not self.link_allowed():
            return

        try:
            number = int(value)

        except ValueError:
            print(
                "\nUsage: link NUMBER\n"
            )
            return

        if not 1 <= number <= len(self.links):
            print(
                "\nInvalid link number.\n"
            )
            return

        _, url = self.links[
            number - 1
        ]

        self.load(url)

    # ========================================================
    # HISTORY DISPLAY
    # ========================================================

    def show_history(self):
        if not self.history_allowed():
            return

        if not self.history:
            print(
                "\nHistory is empty.\n"
            )
            return

        print("\nHistory")
        print("-" * 72)

        current = self.history_index

        for index, url in enumerate(
            self.history,
            1,
        ):
            marker = (
                " <-- current"
                if index - 1 == current
                else ""
            )

            print(
                f"{index}. {url}{marker}"
            )

        print()

    # ========================================================
    # HELP
    # ========================================================

    def show_help(self):
        print(
            """
Wrench commands
---------------

URL
    Open an HTML webpage.

link NUMBER
    Open a numbered link.

back
    Go back.

forward
    Go forward.

reload
    Reload the current page.

history
    Show browsing history.

help
    Show this help.

quit
    Exit Wrench.

Security
--------

• HTML only
• No JavaScript execution
• No CSS processing
• No media downloads
• No automatic subresource loading
• No persistent cookies
• Cookies cleared after requests
• No Referer tracking
• No authentication forwarding
• HTTPS certificate verification
• HTTP/HTTPS only
• Local/private network addresses blocked
• Redirect chains limited
• Response size limited
• Render size limited
• Terminal escape sequences stripped
• In-memory HTML cache only
• No credentials stored

Rate limits
-----------

• Global request cooldown
• Per-host request cooldown
• Global request burst limit
• Per-host request burst limit
• Render cooldown
• Link-opening cooldown
• Command burst limit
• History-operation cooldown
"""
        )

    # ========================================================
    # MAIN LOOP
    # ========================================================

    def run(self):
        print("=" * 72)
        print("WRENCH")
        print(
            "Fast, private, security-focused HTML5 browser"
        )
        print("=" * 72)

        print(
            """
HTML only.
No CSS. No JavaScript. No media.

Enter a URL to browse.
Type "help" for commands.
"""
        )

        while True:
            try:
                command = input(
                    "wrench> "
                ).strip()

            except KeyboardInterrupt:
                print(
                    "\n\nExiting Wrench."
                )
                break

            except EOFError:
                print(
                    "\n\nExiting Wrench."
                )
                break

            if not command:
                continue

            if not self.allow_command():
                continue

            lower = command.lower()

            if lower in {
                "quit",
                "exit",
                "q",
            }:
                print(
                    "\nExiting Wrench."
                )
                break

            if lower == "back":
                self.back()
                continue

            if lower == "forward":
                self.forward()
                continue

            if lower in {
                "reload",
                "refresh",
            }:
                if not self.current_url:
                    print(
                        "\nNothing to reload.\n"
                    )
                    continue

                final_url, html = self.fetch(
                    self.current_url,
                    use_cache=False,
                )

                if final_url is None:
                    continue

                self.current_url = final_url

                print(
                    "\n" + "=" * 72
                )
                print(
                    f"{APP_NAME} {VERSION}"
                )
                print(
                    f"URL: {final_url}"
                )
                print(
                    "=" * 72
                )

                self.render(
                    html,
                    final_url,
                )

                continue

            if lower == "history":
                self.show_history()
                continue

            if lower == "help":
                self.show_help()
                continue

            if lower.startswith("link "):
                self.open_link(
                    command[5:].strip()
                )
                continue

            self.load(command)

    # ========================================================
    # CLEANUP
    # ========================================================

    def close(self):
        self.clear_privacy_state()
        self.client.close()


def main():
    browser = Wrench()

    try:
        if len(sys.argv) > 1:
            browser.load(
                sys.argv[1]
            )

        browser.run()

    finally:
        browser.close()


if __name__ == "__main__":
    main()
