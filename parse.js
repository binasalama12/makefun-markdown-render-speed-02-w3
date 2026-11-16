// SwiftMark w3 — a single-pass streaming Markdown -> HTML renderer.
//
// The scanner keeps one explicit cursor into the source. At every block
// boundary it dispatches on the upcoming characters and consumes exactly
// one construct (fence, heading, rule, quote, list, HTML block, reference
// definition, table, setext heading or paragraph) before moving on; it
// never materialises a whole-document token array. Blockquotes and list
// items recurse on their stripped sub-source. Inline markup is rendered
// by a second streaming scanner that walks the block text once and
// resolves escapes, entities, code spans, links, delimiter runs and
// autolinks as it meets them.
import { decodeEntityBody } from "./entities.js";

const RE_BLANK = /^[ \t]*$/;
const RE_FENCE = /^ {0,3}(`{3,}|~{3,})(.*)$/;
const RE_ATX = /^ {0,3}(#{1,6})(?:[ \t]+(.*)|[ \t]*)$/;
const RE_HR = /^ {0,3}(?:(?:\*[ \t]*){3,}|(?:-[ \t]*){3,}|(?:_[ \t]*){3,})$/;
const RE_QUOTE = /^ {0,3}>[ \t]?/;
const RE_SETEXT = /^ {0,3}(=+|-+)[ \t]*$/;
const RE_BULLET = /^([-+*]|\d{1,9}[.)])(?:[ \t]+|[ \t]*$)/;

export function parse(markdown) {
  let src = String(markdown ?? "");
  src = src.replace(/\0/g, "�").replace(/\r\n?/g, "\n");
  const lines = src.split("\n");
  // A trailing newline produces a phantom empty final line; drop it so
  // block consumption sees the same line stream as the reference.
  if (lines.length && lines[lines.length - 1] === "") lines.pop();
  const refs = new Map();
  scanBlocks(lines, refs, false, false);
  return scanBlocks(lines, refs, true, false);
}

// ---------------------------------------------------------------- utils
function escText(s) {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}
function escCode(s) {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}
function escAttr(s) {
  return s
    .replace(/&(?!(?:#[0-9]+|#[xX][0-9a-fA-F]+|[a-zA-Z][a-zA-Z0-9]*);)/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}
function isBlank(l) { return RE_BLANK.test(l); }

// Column width of the first `upto` characters (tabs jump to multiples of 4).
function colWidth(s, upto) {
  let col = 0;
  for (let i = 0; i < upto && i < s.length; i++) {
    if (s[i] === "\t") col += 4 - (col % 4);
    else col++;
  }
  return col;
}
function leadCols(l) {
  let i = 0;
  while (i < l.length && (l[i] === " " || l[i] === "\t")) i++;
  return { cols: colWidth(l, i), idx: i };
}
// Remove up to `n` columns of leading indentation; a partially consumed
// tab is replaced by the spaces that remain of it.
function stripCols(l, n) {
  let col = 0, i = 0;
  while (i < l.length && col < n) {
    const ch = l[i];
    if (ch === " ") { col++; i++; }
    else if (ch === "\t") {
      const w = 4 - (col % 4);
      if (col + w <= n) { col += w; i++; }
      else { return " ".repeat(col + w - n) + l.slice(i + 1); }
    } else break;
  }
  return l.slice(i);
}
function stripUpTo3(l) {
  const { cols, idx } = leadCols(l);
  if (cols <= 3) return l.slice(idx);
  return stripCols(l, 3);
}
function normLabel(s) {
  return s.replace(/\\([!"#$%&'()*+,\-./:;<=>?@[\\\]^_`{|}~])/g, "$1")
    .trim().replace(/\s+/g, " ").toLowerCase();
}

// ------------------------------------------------------- link ref defs
// Try to read one reference definition starting at lines[i]. Returns
// { next, label, href, title } or null. Definitions may span two lines
// (the title may sit on the following line).
function readRefDef(lines, i) {
  const first = lines[i];
  const m = /^ {0,3}\[([^\]]*(?:\\.[^\]]*)*)\]:[ \t]*(.*)$/.exec(first);
  if (!m) return null;
  const label = m[1];
  if (!label.trim()) return null;
  let rest = m[2];
  let used = 1;
  // Destination may be on the next line when rest is empty.
  let guard = 0;
  while (rest.trim() === "" && i + used < lines.length && guard++ < 1) {
    rest = lines[i + used].replace(/^ {0,3}/, "");
    used++;
  }
  const dm = parseDestTitle(rest);
  if (!dm) return null;
  let { href, title, end } = dm;
  let tail = rest.slice(end);
  if (title === undefined) {
    // Title may live on the next line by itself.
    if (tail.trim() === "" && i + used < lines.length) {
      const nxt = lines[i + used];
      const tm = /^ {0,3}("[^"\n]*"|'[^'\n]*'|\([^()\n]*(?:\([^()\n]*\)[^()\n]*)*\))[ \t]*$/.exec(nxt);
      if (tm) { title = tm[1]; used++; tail = ""; }
    }
  }
  if (tail.trim() !== "") return null;
  if (title !== undefined) title = stripTitle(title);
  return { next: i + used, label: normLabel(label), href, title };
}
function stripTitle(t) {
  if (t.startsWith("(")) return t.slice(1, -1).replace(/\\([()\\])/g, "$1");
  return t.slice(1, -1).replace(/\\(["'\\])/g, "$1");
}
// Parse "<dest> title" or "dest title" at the start of s.
function parseDestTitle(s) {
  let i = 0;
  while (i < s.length && (s[i] === " " || s[i] === "\t" || s[i] === "\n")) i++;
  let href;
  if (s[i] === "<") {
    let j = i + 1, out = "";
    let ok = false;
    while (j < s.length) {
      const c = s[j];
      if (c === "\\" && j + 1 < s.length) { out += s[j + 1]; j += 2; continue; }
      if (c === ">") { ok = true; break; }
      if (c === "<" || c === "\n") return null;
      out += c; j++;
    }
    if (!ok) return null;
    href = out; i = j + 1;
  } else {
    let depth = 0, out = "";
    let j = i;
    while (j < s.length) {
      const c = s[j];
      if (c === "\\" && j + 1 < s.length) { out += c + s[j + 1]; j += 2; continue; }
      if (c === "(") { depth++; out += c; j++; continue; }
      if (c === ")") {
        if (depth === 0) break;
        depth--; out += c; j++; continue;
      }
      if (c === " " || c === "\t" || c === "\n" || c < " ") break;
      out += c; j++;
    }
    if (depth !== 0 || out === "") return null;
    href = out.replace(/\\([!"#$%&'()*+,\-./:;<=>?@[\\\]^_`{|}~])/g, "$1");
    i = j;
  }
  let k = i, sawWs = false;
  while (k < s.length && (s[k] === " " || s[k] === "\t" || s[k] === "\n")) { k++; sawWs = true; }
  if (k >= s.length) return { href, title: undefined, end: k };
  if (!sawWs) return null;
  const rest = s.slice(k);
  const tm = /^("[^"\n]*(?:\\.[^"\n]*)*"|'[^'\n]*(?:\\.[^'\n]*)*'|\([^()\n]*(?:\([^()\n]*\)[^()\n]*)*\))/.exec(rest);
  if (!tm) return null;
  return { href, title: tm[1], end: k + tm[1].length };
}

// ------------------------------------------------------------ HTML blocks
const BLOCK_TAGS = new Set(("address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param search section summary table tbody td tfoot th thead title tr track ul").split(" "));
const RE_TAGNAME = /^[A-Za-z][A-Za-z0-9-]*/;
function htmlBlockStart(lines, i, inParagraph) {
  const l = stripUpTo3(lines[i]);
  if (!l.startsWith("<")) return 0;
  const low = l.toLowerCase();
  if (/^<(pre|script|style|textarea)([\s>]|$)/.test(low)) return 1;
  if (l.startsWith("<!--")) return 2;
  if (l.startsWith("<?")) return 3;
  if (/^<![A-Z]/.test(l)) return 4;
  if (l.startsWith("<![CDATA[")) return 5;
  const tm = /^<\/?([A-Za-z][A-Za-z0-9-]*)/.exec(l);
  if (tm && BLOCK_TAGS.has(tm[1].toLowerCase())) {
    const after = l.slice(tm[0].length);
    if (/^[\s>]/.test(after) || /^\/>/.test(after) || after === "") return 6;
  }
  if (!inParagraph) {
    const tag = matchInlineTag(l, 0);
    if (tag && /^[ \t]*$/.test(l.slice(tag.end))) return 7;
  }
  return 0;
}
function htmlBlockEnd(lines, i, type) {
  // returns index just past the last line of the block starting at i
  let j = i;
  if (type === 1) {
    const close = /<\/(pre|script|style|textarea)>/i;
    while (j < lines.length) { if (close.test(lines[j])) { j++; return j; } j++; }
    return j;
  }
  if (type === 2) { while (j < lines.length) { if (lines[j].includes("-->")) { j++; return j; } j++; } return j; }
  if (type === 3) { while (j < lines.length) { if (lines[j].includes("?>")) { j++; return j; } j++; } return j; }
  if (type === 4) { while (j < lines.length) { if (lines[j].includes(">")) { j++; return j; } j++; } return j; }
  if (type === 5) { while (j < lines.length) { if (lines[j].includes("]]>")) { j++; return j; } j++; } return j; }
  while (j < lines.length && !isBlank(lines[j])) j++;
  return j;
}

// Inline tag matcher shared by block type 7 and the inline scanner.
// Returns { end, raw } or null.
function matchInlineTag(s, i) {
  const rest = s.slice(i);
  let m;
  if ((m = /^<!--/.exec(rest))) {
    if (rest.startsWith("<!-->")) return { end: i + 5, raw: "<!-->" };
    if (rest.startsWith("<!--->")) return { end: i + 6, raw: "<!--->" };
    const e = rest.indexOf("-->", 4);
    if (e === -1) return null;
    const body = rest.slice(4, e);
    if (body.includes("--") || body.endsWith("-")) return null;
    return { end: i + e + 3, raw: rest.slice(0, e + 3) };
  }
  if ((m = /^<\?/.exec(rest))) {
    const e = rest.indexOf("?>", 2);
    if (e === -1) return null;
    return { end: i + e + 2, raw: rest.slice(0, e + 2) };
  }
  if ((m = /^<![CDATA\[/.exec(rest))) {
    const e = rest.indexOf("]]>", 9);
    if (e === -1) return null;
    return { end: i + e + 3, raw: rest.slice(0, e + 3) };
  }
  if ((m = /^<![A-Z]+/.exec(rest))) {
    const e = rest.indexOf(">", m[0].length);
    if (e === -1) return null;
    return { end: i + e + 1, raw: rest.slice(0, e + 1) };
  }
  if ((m = /^<\/([A-Za-z][A-Za-z0-9-]*)[ \t]*>/.exec(rest))) {
    return { end: i + m[0].length, raw: m[0] };
  }
  if ((m = /^<([A-Za-z][A-Za-z0-9-]*)/.exec(rest))) {
    let j = m[0].length;
    for (;;) {
      const ws = /^[ \t\n]+/.exec(rest.slice(j));
      if (!ws) break;
      j += ws[0].length;
      if (rest[j] === ">" || (rest[j] === "/" && rest[j + 1] === ">")) break;
      const am = /^[A-Za-z_:][A-Za-z0-9_.:-]*/.exec(rest.slice(j));
      if (!am) return null;
      j += am[0].length;
      const eq = /^[ \t\n]*=[ \t\n]*/.exec(rest.slice(j));
      if (eq) {
        j += eq[0].length;
        const q = rest[j];
        if (q === '"' || q === "'") {
          const e = rest.indexOf(q, j + 1);
          if (e === -1) return null;
          j = e + 1;
        } else {
          const vm = /^[^\s"'=<>`]+/.exec(rest.slice(j));
          if (!vm) return null;
          j += vm[0].length;
        }
      }
    }
    while (rest[j] === " " || rest[j] === "\t" || rest[j] === "\n") j++;
    if (rest[j] === "/" && rest[j + 1] === ">") return { end: i + j + 2, raw: rest.slice(0, j + 2) };
    if (rest[j] === ">") return { end: i + j + 1, raw: rest.slice(0, j + 1) };
    return null;
  }
  return null;
}

// ---------------------------------------------------------------- tables
function splitRow(line) {
  // Split a table row on unescaped pipes outside code spans.
  let s = line.trim();
  if (s.startsWith("|")) s = s.slice(1);
  let endsWithPipe = false;
  if (s.endsWith("|") && !s.endsWith("\\|")) endsWithPipe = true;
  if (endsWithPipe) s = s.slice(0, -1);
  const cells = [];
  let cur = "", ticks = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === "\\" && s[i + 1] === "|") { cur += "|"; i++; continue; }
    if (c === "`") {
      let n = 0; while (s[i + n] === "`") n++;
      if (ticks === 0) ticks = n; else if (n === ticks) ticks = 0;
      cur += "`".repeat(n); i += n - 1; continue;
    }
    if (c === "|" && ticks === 0) { cells.push(cur); cur = ""; continue; }
    cur += c;
  }
  cells.push(cur);
  return cells.map((c) => c.trim());
}
function tableAligns(line, count) {
  const cells = splitRow(line);
  if (cells.length !== count) return null;
  const aligns = [];
  for (const c of cells) {
    if (!/^:?-+:?$/.test(c)) return null;
    const l = c.startsWith(":"), r = c.endsWith(":");
    aligns.push(l && r ? "center" : l ? "left" : r ? "right" : null);
  }
  return aligns;
}

// ---------------------------------------------------------- block scanner
// tightPara: paragraphs at this level render without <p> wrappers
// (used for items of a tight list).
function scanBlocks(lines, refs, render, tightPara) {
  let out = "";
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (isBlank(line)) { i++; continue; }
    const lead = leadCols(line).cols;

    // Fenced code.
    if (lead <= 3) {
      const fm = RE_FENCE.exec(line);
      if (fm) {
        const fence = fm[1], ch = fence[0];
        const info = fm[2].trim();
        if (!(ch === "`" && info.includes("`"))) {
          const body = [];
          let j = i + 1;
          const closeRe = new RegExp("^ {0,3}" + (ch === "`" ? "`" : "~") + "{" + fence.length + ",}[ \\t]*$");
          while (j < n && !closeRe.test(lines[j])) { body.push(lines[j]); j++; }
          if (j < n) j++;
          if (render) {
            const lang = info === "" ? "" : info.split(/[ \t]+/)[0];
            const code = body.length ? body.join("\n") + "\n" : "";
            out += "<pre><code" + (lang ? " class=\"language-" + escAttr(lang) + "\"" : "") + ">" + escCode(code) + "</code></pre>\n";
          }
          i = j; continue;
        }
      }
    }

    // Reference definitions (one or more, emitting nothing).
    {
      let j = i, found = false;
      while (j < n) {
        const d = readRefDef(lines, j);
        if (!d) break;
        found = true;
        if (!refs.has(d.label)) refs.set(d.label, { href: d.href, title: d.title });
        j = d.next;
        // definitions may be separated onto following lines directly
        if (j < n && isBlank(lines[j])) break;
      }
      if (found) {
        // If text remains on the same block it becomes a paragraph below.
        if (j >= n || isBlank(lines[j])) { i = j; continue; }
        i = j;
        // fall through with the remainder as a fresh block start
        const rem = scanBlocks(lines.slice(i), refs, render, tightPara);
        return out + rem;
      }
    }

    // ATX heading.
    if (lead <= 3) {
      const am = RE_ATX.exec(line);
      if (am) {
        if (render) {
          let text = (am[2] ?? "").replace(/[ \t]+$/, "");
          text = text.replace(/[ \t]+#+$/, "");
          if (/^#+$/.test(text)) text = "";
          const lvl = am[1].length;
          out += "<h" + lvl + ">" + renderInline(text.trim(), refs, false) + "</h" + lvl + ">\n";
        }
        i++; continue;
      }
      if (RE_HR.test(line)) { if (render) out += "<hr>\n"; i++; continue; }
    }

    // Blockquote.
    if (lead <= 3 && RE_QUOTE.test(line)) {
      const inner = [];
      let j = i;
      while (j < n) {
        const l = lines[j];
        const qm = RE_QUOTE.exec(l);
        if (qm) { inner.push(l.slice(qm[0].length)); j++; continue; }
        if (isBlank(l)) {
          // Blank without a marker belongs to the quote only when a
          // later line resumes the quote.
          let k = j + 1;
          if (k < n && RE_QUOTE.test(lines[k])) { inner.push(""); j++; continue; }
          break;
        }
        // Laziness: a plain continuation line joins the quote when the
        // inner tail is an open paragraph and the line cannot start a
        // block that would interrupt that paragraph.
        if (inner.length && !isBlank(inner[inner.length - 1]) && lazyOk(l, inner)) {
          inner.push(stripUpTo3(l)); j++; continue;
        }
        break;
      }
      if (render) out += "<blockquote>\n" + scanBlocks(inner, refs, true, false) + "</blockquote>\n";
      else scanBlocks(inner, refs, false, false);
      i = j; continue;
    }

    // HTML block.
    if (lead <= 3) {
      const t = htmlBlockStart(lines, i, false);
      if (t) {
        const j = htmlBlockEnd(lines, i, t);
        if (render) out += lines.slice(i, j).join("\n") + "\n";
        i = j; continue;
      }
    }

    // List.
    if (lead <= 3) {
      const lm = matchListMarker(line);
      if (lm) {
        const res = readList(lines, i, refs, render);
        out += res.html; i = res.next; continue;
      }
    }

    // Indented code (never interrupts a paragraph; we are at a boundary).
    if (lead >= 4) {
      const body = [];
      let j = i;
      while (j < n) {
        const l = lines[j];
        if (isBlank(l)) { body.push(""); j++; continue; }
        if (leadCols(l).cols >= 4) { body.push(stripCols(l, 4)); j++; continue; }
        break;
      }
      while (body.length && body[body.length - 1] === "") body.pop();
      if (render) out += "<pre><code>" + escCode(body.join("\n") + "\n") + "</code></pre>\n";
      i = j; continue;
    }

    // Paragraph, setext heading or table: buffer one block.
    const res = readParagraph(lines, i, refs, render, tightPara);
    out += res.html; i = res.next;
  }
  return out;
}
function lazyOk(l, inner) {
  if (RE_FENCE.test(l) || RE_ATX.test(l) || RE_QUOTE.test(l)) return false;
  if (htmlBlockStart([l], 0, true)) return false;
  const lm = matchListMarker(l);
  if (lm && (lm.bullet !== null || lm.start === 1) && lm.hasContent) return false;
  return true;
}

// ------------------------------------------------------------- list items
function matchListMarker(line) {
  const lead = leadCols(line);
  if (lead.cols > 3) return null;
  const rest = line.slice(lead.idx);
  const m = RE_BULLET.exec(rest);
  if (!m) return null;
  const marker = m[1];
  const bullet = /^[+\-*]$/.test(marker) ? marker : null;
  let start = null, delim = null;
  if (bullet === null) {
    delim = marker[marker.length - 1];
    start = parseInt(marker.slice(0, -1), 10);
  }
  const after = rest.slice(m[0].length);
  const spCols = m[0].length - marker.length; // includes the gap columns approx
  const gapText = rest.slice(marker.length, m[0].length);
  const gapCols = colWidth(gapText, gapText.length);
  return {
    indent: lead.cols, marker, bullet, start, delim,
    markerWidth: marker.length, gapCols,
    hasContent: after.trim() !== "",
    after, lineRest: rest,
  };
}
function sameList(a, b) {
  if (a.bullet !== null || b.bullet !== null) return a.bullet === b.bullet;
  return a.delim === b.delim;
}
function readList(lines, i, refs, render) {
  const first = matchListMarker(lines[i]);
  const items = [];
  let loose = false;
  let j = i;
  let startNum = first.start;
  while (j < lines.length) {
    const lm = matchListMarker(lines[j]);
    if (!lm || !sameList(first, lm)) break;
    // Content indent for this item.
    let contentIndent;
    if (!lm.hasContent && lm.gapCols === 0) contentIndent = lm.indent + lm.markerWidth + 1;
    else if (lm.gapCols >= 5 || !lm.hasContent) contentIndent = lm.indent + lm.markerWidth + 1;
    else contentIndent = lm.indent + lm.markerWidth + lm.gapCols;
    const itemLines = [];
    let firstContent;
    if (!lm.hasContent && lm.gapCols === 0) firstContent = "";
    else if (lm.gapCols >= 5) firstContent = stripCols(lines[j], lm.indent + lm.markerWidth + 1);
    else firstContent = stripCols(lines[j], contentIndent);
    itemLines.push(firstContent);
    j++;
    let itemBlank = false;   // saw a blank line inside this item
    let endedByBlank = false;
    while (j < lines.length) {
      const l = lines[j];
      if (isBlank(l)) {
        // Look ahead: does the item continue, does the list continue?
        let k = j;
        while (k < lines.length && isBlank(lines[k])) k++;
        if (k >= lines.length) { j = k; endedByBlank = true; break; }
        const nl = lines[k];
        const nlead = leadCols(nl).cols;
        const nlm = matchListMarker(nl);
        if (nlead >= contentIndent) {
          for (let b = j; b < k; b++) itemLines.push("");
          itemBlank = true; loose = true; j = k; continue;
        }
        if (nlm && sameList(first, nlm) && nlm.indent <= lm.indent + 3 && nlead < contentIndent) {
          endedByBlank = true; j = k; break;
        }
        if (k - j >= 2) { endedByBlank = true; j = k; break; }
        // A single blank then a lazy line still belongs to the item
        // only when the item has an open paragraph; treat as end.
        endedByBlank = true; j = k; break;
      }
      const lc = leadCols(l).cols;
      if (lc >= contentIndent) { itemLines.push(stripCols(l, contentIndent)); j++; continue; }
      const nlm = matchListMarker(l);
      if (nlm && sameList(first, nlm)) break;
      // Lazy continuation of an open paragraph inside the item.
      if (itemLines.length && !isBlank(itemLines[itemLines.length - 1]) && lazyOk(l, itemLines)) {
        itemLines.push(stripUpTo3(l)); j++; continue;
      }
      break;
    }
    // Trailing blank lines inside the item do not count as looseness
    // unless another item follows.
    while (itemLines.length && isBlank(itemLines[itemLines.length - 1])) itemLines.pop();
    items.push(itemLines);
    if (endedByBlank && j < lines.length && matchListMarker(lines[j]) && sameList(first, matchListMarker(lines[j]))) loose = true;
    if (itemBlank) loose = true;
    if (!(j < lines.length && matchListMarker(lines[j]) && sameList(first, matchListMarker(lines[j])))) break;
  }
  if (!render) {
    for (const it of items) scanBlocks(it, refs, false, false);
    return { html: "", next: j };
  }
  const ordered = first.bullet === null;
  let html = ordered ? (startNum !== 1 ? "<ol start=\"" + startNum + "\">\n" : "<ol>\n") : "<ul>\n";
  for (const it of items) {
    let task = null;
    if (it.length && /^\[( |x|X)\](?:[ \t]|$)/.test(it[0])) {
      task = it[0][1] !== " ";
      it[0] = it[0].slice(3);
    }
    let body = scanBlocks(it, refs, true, !loose);
    body = body.replace(/\n$/, "");
    let li = "<li>";
    if (task !== null) {
      li += task ? "<input checked=\"\" disabled=\"\" type=\"checkbox\">" : "<input disabled=\"\" type=\"checkbox\">";
      if (body !== "" && !body.startsWith("<")) li += "";
    }
    html += li + body + "</li>\n";
  }
  html += ordered ? "</ol>\n" : "</ul>\n";
  return { html, next: j };
}

// ------------------------------------------------------- paragraph blocks
function interruptsParagraph(lines, j) {
  const l = lines[j];
  const lead = leadCols(l).cols;
  if (lead > 3) return false;
  if (RE_FENCE.test(l)) return true;
  if (RE_ATX.test(l)) return true;
  if (RE_QUOTE.test(l)) return true;
  if (RE_HR.test(l)) return true;
  const t = htmlBlockStart(lines, j, true);
  if (t >= 1 && t <= 6) return true;
  const lm = matchListMarker(l);
  if (lm && lm.hasContent && (lm.bullet !== null || lm.start === 1)) {
    // An empty-ish or thematic-looking bullet does not interrupt.
    return true;
  }
  return false;
}
function readParagraph(lines, i, refs, render, tightPara) {
  // Table check: first line plus a delimiter second line.
  if (i + 1 < lines.length && lines[i].includes("|") || (i + 1 < lines.length && !isBlank(lines[i + 1]))) {
    if (i + 1 < lines.length) {
      const headerCells = splitRow(lines[i]);
      const aligns = tableAligns(lines[i + 1], headerCells.length);
      if (aligns && headerCells.length > 0 && lines[i].trim() !== "") {
        const rows = [];
        let j = i + 2;
        while (j < lines.length && !isBlank(lines[j])) {
          // A row line that clearly starts another block ends the table.
          if (j > i + 2 && (RE_FENCE.test(lines[j]) || RE_QUOTE.test(lines[j]))) break;
          const cells = splitRow(lines[j]);
          while (cells.length < headerCells.length) cells.push("");
          rows.push(cells.slice(0, headerCells.length));
          j++;
        }
        if (!render) return { html: "", next: j };
        let html = "<table>\n<thead>\n<tr>\n";
        headerCells.forEach((c, k) => {
          html += "<th" + (aligns[k] ? " align=\"" + aligns[k] + "\"" : "") + ">" + renderInline(c, refs, false) + "</th>\n";
        });
        html += "</tr>\n</thead>\n";
        if (rows.length) {
          html += "<tbody>\n";
          for (const r of rows) {
            html += "<tr>\n";
            r.forEach((c, k) => {
              html += "<td" + (aligns[k] ? " align=\"" + aligns[k] + "\"" : "") + ">" + renderInline(c, refs, false) + "</td>\n";
            });
            html += "</tr>\n";
          }
          html += "</tbody>\n";
        }
        html += "</table>\n";
        return { html, next: j };
      }
    }
  }
  const buf = [lines[i]];
  let j = i + 1;
  let setext = 0;
  while (j < lines.length) {
    const l = lines[j];
    if (isBlank(l)) break;
    const sm = RE_SETEXT.exec(l);
    if (sm && leadCols(l).cols <= 3) { setext = sm[1][0] === "=" ? 1 : 2; j++; break; }
    if (interruptsParagraph(lines, j)) break;
    buf.push(l); j++;
  }
  if (!render) return { html: "", next: j };
  const text = buf.map((l) => stripUpTo3(l)).join("\n");
  if (setext) return { html: "<h" + setext + ">" + renderInline(text, refs, false) + "</h" + setext + ">\n", next: j };
  const inner = renderInline(text, refs, false);
  if (tightPara) return { html: inner + "\n", next: j };
  return { html: "<p>" + inner + "</p>\n", next: j };
}

// --------------------------------------------------------- inline scanner
const ASCII_PUNCT = "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~";
function isWsCh(c) { return c === undefined || c === "" || /\s/.test(c); }
function isPunctCh(c) {
  if (c === undefined || c === "") return false;
  return /[\p{P}\p{S}]/u.test(c);
}
function nodesToHtml(nodes) {
  let out = "";
  for (const nd of nodes) {
    if (nd.t === "text") out += escText(nd.s);
    else if (nd.t === "html") out += nd.s;
    else if (nd.t === "delim") out += nd.ch.repeat(nd.n);
  }
  return out;
}
function plainAlt(nodesHtml) {
  const stripped = nodesHtml.replace(/<[^>]*>/g, "");
  return stripped.replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, "\"").replace(/&amp;/g, "&");
}

function renderInline(s, refs, inLink) {
  const nodes = [];
  let buf = "";
  const flush = () => { if (buf) { nodes.push({ t: "text", s: buf }); buf = ""; } };
  let i = 0;
  const n = s.length;
  while (i < n) {
    const c = s[i];
    if (c === "\\") {
      const nx = s[i + 1];
      if (nx === "\n") { flush(); nodes.push({ t: "html", s: "<br>\n" }); i += 2; continue; }
      if (nx !== undefined && ASCII_PUNCT.includes(nx)) { buf += nx; i += 2; continue; }
      buf += "\\"; i++; continue;
    }
    if (c === "\n") {
      let sp = 0;
      while (buf[buf.length - 1 - sp] === " ") sp++;
      if (sp >= 2) { buf = buf.slice(0, buf.length - sp); flush(); nodes.push({ t: "html", s: "<br>\n" }); }
      else { buf += "\n"; }
      i++; continue;
    }
    if (c === "`") {
      let run = 0; while (s[i + run] === "`") run++;
      const needle = "`".repeat(run);
      let found = -1;
      for (let j = i + run; j < n;) {
        const k = s.indexOf(needle, j);
        if (k === -1) break;
        // must be a run of exactly `run` ticks
        let r2 = 0; while (s[k + r2] === "`") r2++;
        if (r2 === run && s[k - 1] !== "`") { found = k; break; }
        j = k + r2;
      }
      if (found === -1) { buf += needle; i += run; continue; }
      let code = s.slice(i + run, found).replace(/\n/g, " ");
      if (code.length >= 2 && code.startsWith(" ") && code.endsWith(" ") && code.trim() !== "") code = code.slice(1, -1);
      flush();
      nodes.push({ t: "html", s: "<code>" + escCode(code) + "</code>" });
      i = found + run; continue;
    }
    if (c === "&") {
      const em = /^&(#(?:[xX][0-9a-fA-F]+|[0-9]+)|[a-zA-Z][a-zA-Z0-9]*);/.exec(s.slice(i, i + 34));
      if (em) {
        const dec = decodeEntityBody(em[1]);
        if (dec !== null) { buf += dec; i += em[0].length; continue; }
      }
      buf += "&"; i++; continue;
    }
    if (c === "<") {
      const rest = s.slice(i);
      const am = /^<([A-Za-z][A-Za-z0-9+.-]{1,31}:[^<>\s]*)>/.exec(rest);
      if (am) {
        flush();
        nodes.push({ t: "html", s: "<a href=\"" + escAttr(am[1]) + "\">" + escText(am[1]) + "</a>" });
        i += am[0].length; continue;
      }
      const mm = /^<([A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+)>/.exec(rest);
      if (mm) {
        flush();
        nodes.push({ t: "html", s: "<a href=\"mailto:" + escAttr(mm[1]) + "\">" + escText(mm[1]) + "</a>" });
        i += mm[0].length; continue;
      }
      const tag = matchInlineTag(s, i);
      if (tag) { flush(); nodes.push({ t: "html", s: tag.raw }); i = tag.end; continue; }
      buf += "<"; i++; continue;
    }
    if (c === "[" || (c === "!" && s[i + 1] === "[")) {
      const isImg = c === "!";
      const link = tryLink(s, i, isImg, refs, inLink);
      if (link) { flush(); nodes.push({ t: "html", s: link.html }); i = link.end; continue; }
      buf += c; i++; continue;
    }
    if (c === "*" || c === "_" || c === "~") {
      let run = 0; while (s[i + run] === c) run++;
      if (c === "~" && run === 1 && s[i + 1] === "~") { /* unreachable */ }
      const before = i > 0 ? s[i - 1] : undefined;
      const after = i + run < n ? s[i + run] : undefined;
      const bWs = isWsCh(before), aWs = isWsCh(after);
      const bP = isPunctCh(before), aP = isPunctCh(after);
      const left = !aWs && (!aP || bWs || bP);
      const right = !bWs && (!bP || aWs || aP);
      let canOpen, canClose;
      if (c === "_") { canOpen = left && (!right || bP); canClose = right && (!left || aP); }
      else { canOpen = left; canClose = right; }
      if (c === "~" && run > 2) { buf += "~".repeat(run); i += run; continue; }
      flush();
      nodes.push({ t: "delim", ch: c, n: run, canOpen, canClose });
      i += run; continue;
    }
    if (!inLink && (c === "h" || c === "w" || c === "f")) {
      const auto = tryExtAutolink(s, i);
      if (auto) { flush(); nodes.push({ t: "html", s: auto.html }); i = auto.end; continue; }
    }
    if (!inLink && /[A-Za-z0-9]/.test(c)) {
      const em2 = tryEmailAutolink(s, i);
      if (em2) { flush(); nodes.push({ t: "html", s: em2.html }); i = em2.end; continue; }
    }
    buf += c; i++;
  }
  flush();
  processDelims(nodes);
  return nodesToHtml(nodes);
}

function prevBoundaryOk(s, i) {
  if (i === 0) return true;
  const p = s[i - 1];
  return /\s/.test(p) || "([{\"'*_~<".includes(p);
}
function trimUrl(u) {
  let prev = null;
  while (prev !== u && u.length) {
    prev = u;
    const ent = /&[A-Za-z0-9]+;$/.exec(u);
    if (ent) { u = u.slice(0, ent.index); continue; }
    const last = u[u.length - 1];
    if ("?!.,:*_~'\"".includes(last)) { u = u.slice(0, -1); continue; }
    if (last === ")") {
      const opens = (u.match(/\(/g) || []).length;
      const closes = (u.match(/\)/g) || []).length;
      if (closes > opens) { u = u.slice(0, -1); continue; }
    }
    if (last === "]") {
      const opens = (u.match(/\[/g) || []).length;
      const closes = (u.match(/\]/g) || []).length;
      if (closes > opens) { u = u.slice(0, -1); continue; }
    }
  }
  return u;
}
function tryExtAutolink(s, i) {
  if (!prevBoundaryOk(s, i)) return null;
  const rest = s.slice(i);
  const m = /^(?:https?:\/\/|www\.)[^\s<]+/.exec(rest);
  if (!m) return null;
  let url = trimUrl(m[0]);
  const isWww = url.startsWith("www.");
  const afterProto = isWww ? url.slice(4) : url.replace(/^https?:\/\//, "");
  const host = afterProto.split(/[/?#]/)[0];
  if (!host.includes(".")) return null;
  if (!/^[A-Za-z0-9_-]+(?:\.[A-Za-z0-9_-]+)+$/.test(host.replace(/:\d+$/, ""))) {
    // allow ports and userinfo-free hosts only in the simple shape
    if (!/^[A-Za-z0-9_-]+(?:\.[A-Za-z0-9_-]+)+:\d+$/.test(host)) return null;
  }
  if (url.length <= (isWww ? 4 : 7)) return null;
  const href = isWww ? "http://" + url : url;
  return { html: "<a href=\"" + escAttr(href) + "\">" + escText(url) + "</a>", end: i + url.length };
}
function tryEmailAutolink(s, i) {
  if (!prevBoundaryOk(s, i)) return null;
  const rest = s.slice(i);
  const m = /^[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?)+/.exec(rest);
  if (!m) return null;
  const email = m[0];
  if (email.startsWith(".") || email.includes("..")) return null;
  return { html: "<a href=\"mailto:" + escAttr(email) + "\">" + escText(email) + "</a>", end: i + email.length };
}

// ------------------------------------------------------------ link syntax
function findCloseBracket(s, open) {
  let depth = 0;
  let i = open;
  while (i < s.length) {
    const c = s[i];
    if (c === "\\") { i += 2; continue; }
    if (c === "`") { let r = 0; while (s[i + r] === "`") r++; const k = s.indexOf("`".repeat(r), i + r); if (k !== -1) { i = k + r; continue; } i += r; continue; }
    if (c === "[") depth++;
    if (c === "]") { depth--; if (depth === 0) return i; }
    i++;
  }
  return -1;
}
function parseInlineDest(s, pos) {
  // pos is just after '('
  let i = pos;
  const skipWs = () => { while (i < s.length && /\s/.test(s[i])) i++; };
  skipWs();
  let href;
  if (s[i] === "<") {
    let j = i + 1, out = "", ok = false;
    while (j < s.length) {
      const c = s[j];
      if (c === "\\" && j + 1 < s.length) { out += s[j + 1]; j += 2; continue; }
      if (c === ">") { ok = true; break; }
      if (c === "<" || c === "\n") return null;
      out += c; j++;
    }
    if (!ok) return null;
    href = out; i = j + 1;
  } else {
    let depth = 0, out = "";
    while (i < s.length) {
      const c = s[i];
      if (c === "\\" && i + 1 < s.length) { out += c + s[i + 1]; i += 2; continue; }
      if (c === "(") { depth++; out += c; i++; continue; }
      if (c === ")") { if (depth === 0) break; depth--; out += c; i++; continue; }
      if (/\s/.test(c) || c < " ") break;
      out += c; i++;
    }
    if (depth !== 0) return null;
    href = out.replace(/\\([!"#$%&'()*+,\-./:;<=>?@[\\\]^_`{|}~])/g, "$1");
  }
  const beforeWs = i;
  skipWs();
  let title;
  if (s[i] !== ")") {
    if (i === beforeWs) return null;
    const rest = s.slice(i);
    const tm = /^("[^"\n]*(?:\\.[^"\n]*)*"|'[^'\n]*(?:\\.[^'\n]*)*'|\([^()\n]*(?:\([^()\n]*\)[^()\n]*)*\))/.exec(rest);
    if (!tm) return null;
    title = stripTitle(tm[1]);
    i += tm[1].length;
    skipWs();
  }
  if (s[i] !== ")") return null;
  return { href, title, end: i + 1 };
}
function tryLink(s, i, isImg, refs, inLink) {
  const open = isImg ? i + 1 : i;
  const close = findCloseBracket(s, open);
  if (close === -1) return null;
  const text = s.slice(open + 1, close);
  let href, title, end;
  const after = close + 1;
  if (s[after] === "(") {
    const d = parseInlineDest(s, after + 1);
    if (!d) return null;
    href = d.href; title = d.title; end = d.end;
  } else if (s[after] === "[") {
    const close2 = findCloseBracket(s, after);
    if (close2 === -1) return null;
    const lab = s.slice(after + 1, close2);
    const key = normLabel(lab === "" ? text : lab);
    const def = refs.get(key);
    if (!def) return null;
    href = def.href; title = def.title; end = close2 + 1;
  } else {
    const key = normLabel(text);
    const def = key ? refs.get(key) : undefined;
    if (!def) return null;
    href = def.href; title = def.title; end = after;
  }
  if (isImg) {
    const alt = plainAlt(renderInline(text, refs, true));
    let html = "<img src=\"" + escAttr(href) + "\" alt=\"" + escAttr(alt) + "\"";
    if (title !== undefined) html += " title=\"" + escAttr(title) + "\"";
    return { html: html + ">", end };
  }
  if (inLink) return null;
  const inner = renderInline(text, refs, true);
  let html = "<a href=\"" + escAttr(href) + "\"";
  if (title !== undefined) html += " title=\"" + escAttr(title) + "\"";
  return { html: html + ">" + inner + "</a>", end };
}

// ------------------------------------------------------ delimiter pairing
function processDelims(nodes) {
  for (;;) {
    let acted = false;
    for (let ci = 0; ci < nodes.length; ci++) {
      const closer = nodes[ci];
      if (closer.t !== "delim" || !closer.canClose || closer.n === 0) continue;
      let oi = -1;
      for (let k = ci - 1; k >= 0; k--) {
        const op = nodes[k];
        if (op.t !== "delim" || op.ch !== closer.ch || !op.canOpen || op.n === 0) continue;
        const odd = (closer.canOpen || op.canClose) &&
          ((op.n + closer.n) % 3 === 0) && !(op.n % 3 === 0 && closer.n % 3 === 0);
        if (odd) continue;
        oi = k; break;
      }
      if (oi === -1) continue;
      const opener = nodes[oi];
      const use = opener.n >= 2 && closer.n >= 2 ? 2 : 1;
      const tag = closer.ch === "~" ? "del" : use === 2 ? "strong" : "em";
      const seg = nodes.splice(oi + 1, ci - oi - 1);
      const html = "<" + tag + ">" + nodesToHtml(seg) + "</" + tag + ">";
      nodes.splice(oi + 1, 0, { t: "html", s: html });
      opener.n -= use; closer.n -= use;
      if (closer.n === 0) nodes.splice(oi + 2 + (opener.n === 0 ? -1 : 0) + 1 - 1, 0); // no-op keep indices simple
      // Remove zero-count delimiters.
      for (let k = nodes.length - 1; k >= 0; k--) {
        if (nodes[k].t === "delim" && nodes[k].n === 0) nodes.splice(k, 1);
      }
      acted = true;
      break;
    }
    if (!acted) return;
  }
}
