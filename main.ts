// SwiftMark w3 driver: render every case in /input/cases.json with the
// streaming parser and write the HTML strings, in order, to
// /output/html.json.
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { parse } from "./parse.js";

interface Case {
  id: string;
  markdown: string;
}

const raw = readFileSync("/input/cases.json", "utf8");
const cases = JSON.parse(raw) as Case[];
const out: string[] = [];
for (const c of cases) {
  out.push(parse(c.markdown));
}
mkdirSync("/output", { recursive: true });
writeFileSync("/output/html.json", JSON.stringify(out));
