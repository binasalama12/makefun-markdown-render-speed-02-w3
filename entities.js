// Compact named-entity table for the streaming renderer.
// Keys are entity names without the surrounding & and ; characters.
// Numeric references are decoded arithmetically and never consult this
// table; the table backs validation-style lookups for named references.
const RAW = "amp:& lt:< gt:> quot:\" apos:' nbsp:  iexcl:¡ cent:¢ pound:£ curren:¤ yen:¥ brvbar:¦ sect:§ uml:¨ copy:© ordf:ª laquo:« not:¬ shy:­ reg:® macr:¯ deg:° plusmn:± sup2:² sup3:³ acute:´ micro:µ para:¶ middot:· cedil:¸ sup1:¹ ordm:º raquo:» frac14:¼ frac12:½ frac34:¾ iquest:¿ Agrave:À Aacute:Á Acirc:Â Atilde:Ã Auml:Ä Aring:Å AElig:Æ Ccedil:Ç Egrave:È Eacute:É Ecirc:Ê Euml:Ë Igrave:Ì Iacute:Í Icirc:Î Iuml:Ï ETH:Ð Ntilde:Ñ Ograve:Ò Oacute:Ó Ocirc:Ô Otilde:Õ Ouml:Ö times:× Oslash:Ø Ugrave:Ù Uacute:Ú Ucirc:Û Uuml:Ü Yacute:Ý THORN:Þ szlig:ß agrave:à aacute:á acirc:â atilde:ã auml:ä aring:å aelig:æ ccedil:ç egrave:è eacute:é ecirc:ê euml:ë igrave:ì iacute:í icirc:î iuml:ï eth:ð ntilde:ñ ograve:ò oacute:ó ocirc:ô otilde:õ ouml:ö divide:÷ oslash:ø ugrave:ù uacute:ú ucirc:û uuml:ü yacute:ý thorn:þ yuml:ÿ OElig:Œ oelig:œ Scaron:Š scaron:š Yuml:Ÿ fnof:ƒ circ:ˆ tilde:˜ ensp:  emsp:  thinsp:  zwnj:‌ zwj:‍ lrm:‎ rlm:‏ ndash:– mdash:— lsquo:‘ rsquo:’ sbquo:‚ ldquo:“ rdquo:” bdquo:„ dagger:† Dagger:‡ bull:• hellip:… permil:‰ prime:′ Prime:″ lsaquo:‹ rsaquo:› oline:‾ frasl:⁄ euro:€ image:ℑ letter:℘ script:𝒫 weierp:℘ real:ℜ trade:™ alefsym:ℵ larr:← uarr:↑ rarr:→ darr:↓ harr:↔ crarr:↵ lArr:⇐ uArr:⇑ rArr:⇒ dArr:⇓ hArr:⇔ forall:∀ part:∂ exist:∃ empty:∅ nabla:∇ isin:∈ notin:∉ ni:∋ prod:∏ sum:∑ minus:− lowast:∗ radic:√ prop:∝ infin:∞ ang:∠ and:∧ or:∨ cap:∩ cup:∪ int:∫ there4:∴ sim:∼ cong:≅ asymp:≈ ne:≠ equiv:≡ le:≤ ge:≥ sub:⊂ sup:⊃ nsub:⊄ sube:⊆ supe:⊇ oplus:⊕ otimes:⊗ perp:⊥ sdots:⋅ lceil:⌈ rceil:⌉ lfloor:⌊ rfloor:⌋ lang:⟨ rang:⟩ loz:◊ spades:♠ clubs:♣ hearts:♥ diams:♦ alpha:α beta:β gamma:γ delta:δ epsilon:ε zeta:ζ eta:η theta:θ iota:ι kappa:κ lambda:λ mu:μ nu:ν xi:ξ omicron:ο pi:π rho:ρ sigmaf:ς sigma:σ tau:τ upsilon:υ phi:φ chi:χ psi:ψ omega:ω Alpha:Α Beta:Β Gamma:Γ Delta:Δ Epsilon:Ε Zeta:Ζ Eta:Η Theta:Θ Iota:Ι Kappa:Κ Lambda:Λ Mu:Μ Nu:Ν Xi:Ξ Omicron:Ο Pi:Π Rho:Ρ Sigma:Σ Tau:Τ Upsilon:Υ Phi:Φ Chi:Χ Psi:Ψ Omega:Ω thetasym:ϑ upsih:ϒ piv:ϖ ensp2: ";
export const ENTITIES = Object.create(null);
for (const pair of RAW.split(" ")) {
  const cut = pair.indexOf(":");
  if (cut > 0) ENTITIES[pair.slice(0, cut)] = pair.slice(cut + 1);
}
// A handful of long-tail names that show up in spec examples.
Object.assign(ENTITIES, {
  Aopf: "𝔸", aopf: "𝕒", NotEqualTilde: "≂̸", fjlig: "fj", HilbertSpace: "ℋ",
  Hscr: "ℋ", ImaginaryI: "ⅈ", imagpart: "ℑ", Lscr: "ℒ", Mscr: "ℳ",
  Tab: "\t", NewLine: "\n", colon: ":", semi: ";", comma: ",", period: ".",
  excl: "!", quest: "?", at: "@", sol: "/", bsol: "\\", Hat: "^",
  lowbar: "_", grave: "`", lbrace: "{", vert: "|", rbrace: "}", tildeop: "~",
  aacute2: "á", Copy: "©", reg2: "®", GT: ">", LT: "<", AMP: "&", QUOT: "\"",
});
export function decodeEntityBody(body) {
  if (body.startsWith("#")) {
    let cp;
    if (body[1] === "x" || body[1] === "X") {
      if (!/^[0-9a-fA-F]+$/.test(body.slice(2))) return null;
      cp = parseInt(body.slice(2), 16);
    } else {
      if (!/^[0-9]+$/.test(body.slice(1))) return null;
      cp = parseInt(body.slice(1), 10);
    }
    if (cp === 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return "�";
    return String.fromCodePoint(cp);
  }
  return Object.prototype.hasOwnProperty.call(ENTITIES, body) ? ENTITIES[body] : null;
}
