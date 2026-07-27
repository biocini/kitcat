#!/usr/bin/env python3
import re, sys, json, glob, os

MARKETING = ["seamless","seamlessly","robust","powerful","cutting-edge","effortless","effortlessly",
    "world-class","next-generation","revolutionary","blazing","lightning-fast","elegant","delightful",
    "turnkey","best-in-class","state-of-the-art","game-changing","first-class","battle-tested",
    "enterprise-grade","supercharge","unlock","unleash","empower","empowers"]
BANNED = ["begin","begins","commence","commences","initiate","initiates","originate",
    "utilize","utilizes","utilizing","leverage","leverages","leveraging","facilitate","facilitates",
    "ensure","ensures","ensuring","prior to","subsequent to","obtain","obtains","acquire","acquires",
    "demonstrate","demonstrates","additionally","furthermore","moreover","comprehensive","comprehensively",
    "utilization","aforementioned","henceforth","therein","whilst","amongst","numerous","myriad","plethora",
    "in order to","a variety of","in the event that","due to the fact that","it is important to note",
    "load-bearing"]
PHRASAL = ["spin up","spin down","reach out","dive into","dives into","diving into","kick off","kicks off",
    "roll out","rolls out","tear down","ramp up","circle back","drill down","spun up","reaching out"]
MODAL_HEDGE = ["it is important to note","it should be noted","it is worth noting","please note that",
    "as mentioned","as noted above"]
BE = r"(?:am|is|are|was|were|be|been|being)"
PP_IRREG = r"(?:done|made|sent|read|built|kept|held|set|put|run|written|shown|given|taken|found|got|gotten|seen|known|thrown|drawn)"

def strip_code(t):
    # A fenced block is display, not sentence content. An inline code
    # span reads as one noun: one placeholder word, capital so a
    # sentence boundary before it still splits.
    t = re.sub(r"```.*?```", " ", t, flags=re.S)
    t = re.sub(r"`[^`]*`", " X ", t)
    return t

def sentences(text):
    # Hard-wrapped lines join into their paragraph or list item before
    # the split; headers and table rows stand alone.
    out = []
    for block in re.split(r"\n\s*\n", text):
        units, cur = [], []
        for ln in block.split("\n"):
            if re.match(r"\s*(?:[-*+]|\d+[.)])\s+", ln):
                if cur: units.append(" ".join(cur))
                cur = [ln.strip()]
            elif re.match(r"\s*#{1,6}\s", ln) or ln.lstrip().startswith("|"):
                if cur: units.append(" ".join(cur)); cur = []
                units.append(ln.strip())
            else:
                cur.append(ln.strip())
        if cur: units.append(" ".join(cur))
        for s in units:
            s = s.strip()
            if not s: continue
            s = re.sub(r"^#{1,6}\s*", "", s)
            s = re.sub(r"^(?:[-*+]|\d+[.)])\s+", "", s)
            if not s: continue
            for p in re.split(r"(?<=[.!?:])\*{0,2}\s+(?=[A-Z0-9\"'`\-✅🧪📐⚠️])", s):
                p = p.strip()
                if p: out.append(p)
    return out

def wc(s):
    return len([w for w in re.findall(r"[A-Za-z0-9][A-Za-z0-9'\-/]*", s)])

def count_ci(text, phrases):
    n = 0; hits = []
    low = text.lower()
    for ph in phrases:
        for m in re.finditer(r"(?<![a-z])" + re.escape(ph) + r"(?![a-z])", low):
            n += 1; hits.append(ph)
    return n, hits

def lint(text):
    raw = text
    text = strip_code(text)
    sents = sentences(text)
    words = sum(wc(s) for s in sents) or 1
    v = {}
    longs = [(wc(s), s) for s in sents if wc(s) > 20]
    v["long_sentence(>20w)"] = len(longs)
    v["semicolon"] = text.count(";")
    v["contraction"] = (
        len(re.findall(r"\b\w+n['’]t\b", text, re.I))
        + len(re.findall(r"\b\w+['’](?:re|ve|ll|d|m)\b", text, re.I))
        + len(re.findall(r"\b(?:it|that|there|what|here|let|who|one|she|he)['’]s\b", text, re.I)))
    v["passive_voice"] = len(re.findall(rf"\b{BE}\s+(?:\w+ed|{PP_IRREG})\b", text, re.I))
    v["ing_main_verb"] = len(re.findall(rf"\b{BE}\s+\w+ing\b", text, re.I))
    v["nominalization"] = len(re.findall(r"\b(?:perform(?:s|ed)?|conduct(?:s|ed)?|provide(?:s|d)?|carry out|carries out|make use of|makes use of)\b", text, re.I)) + len(re.findall(r"\b\w{4,}(?:tion|ment|ance|ence)\s+of\b", text, re.I))
    v["phrasal_verb"], _ = count_ci(text, PHRASAL)
    v["banned_word"], bh = count_ci(text, BANNED)
    v["marketing_adjective"], mh = count_ci(text, MARKETING)
    v["modal_hedge"], _ = count_ci(text, MODAL_HEDGE)
    v["em_dash"] = text.count("—")
    paras = [p for p in re.split(r"\n\s*\n", raw) if p.strip()]
    def para_sentences(p):
        # A run of list items is a vertical list, not a paragraph.
        kept, in_item = [], False
        for ln in p.split("\n"):
            if re.match(r"\s*(?:[-*+]|\d+[.)])\s+", ln):
                in_item = True
                continue
            if in_item and re.match(r"\s+\S", ln):
                continue
            in_item = False
            kept.append(ln)
        return sentences(strip_code("\n".join(kept)))
    v["long_paragraph(>6s)"] = sum(1 for p in paras if len(para_sentences(p)) > 6)
    total = sum(v.values())
    return {
        "words": words, "sentences": len(sents),
        "violations": v, "total": total,
        "total_per100w": round(total*100.0/words, 2),
        "longest_sentence_words": (max(longs)[0] if longs else max((wc(s) for s in sents), default=0)),
        "sample_marketing": list(dict.fromkeys(mh))[:6],
        "sample_banned": list(dict.fromkeys(bh))[:6],
    }

if __name__ == "__main__":
    args = sys.argv[1:]
    maxp = None
    if "--max-per100" in args:
        i = args.index("--max-per100")
        maxp = float(args[i + 1])
        del args[i:i + 2]
    fail = False
    if not args:
        r = lint(sys.stdin.read())
        print(json.dumps(r, indent=2))
        sys.exit(1 if (maxp is not None and r["total_per100w"] > maxp) else 0)
    exp = []
    for f in args: exp += sorted(glob.glob(f)) if any(c in f for c in "*?[") else [f]
    for f in exp:
        with open(f) as fh: r = lint(fh.read())
        flag = ""
        if maxp is not None and r["total_per100w"] > maxp:
            fail = True
            flag = f"  FAIL(>{maxp})"
        print(f"{f:48} words={r['words']:4d} total={r['total']:3d} per100w={r['total_per100w']:6.2f} em_dash={r['violations']['em_dash']:2d}{flag}")
    sys.exit(1 if fail else 0)
