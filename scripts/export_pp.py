#!/usr/bin/env python3
"""Print declarations of a lean4export (format 3.x) file: export_pp.py FILE NAME..."""
import json,sys
names={0:""};exprs={};decls={}
want=set(sys.argv[2:])
for line in open(sys.argv[1]):
    if line.startswith('{"in"'):
        o=json.loads(line)
        if "str" in o: p,s=o["str"]["pre"],o["str"]["str"]
        else: p,s=o["num"]["pre"],str(o["num"]["i"])
        names[o["in"]]=(names[p]+"."+s) if names[p] else s
    elif '"ie"' in line[:200]:
        i=line.find('"ie":'); j=i+5; k=j
        while line[k].isdigit(): k+=1
        exprs[int(line[j:k])]=line
    else:
        o=json.loads(line)
        for kk in o:
            if isinstance(o[kk],dict) and "name" in o[kk] and names.get(o[kk]["name"]) in want: decls[names[o[kk]["name"]]]=(kk,o[kk])
def E(i): return json.loads(exprs[i])
def pp(i,d):
    if d<=0: return "…"
    e=E(i)
    if "bvar" in e: return f"#{e['bvar']}"
    if "sort" in e: return "Sort"
    if "const" in e: return names[e["const"]["name"]]
    if "app" in e: return f"({pp(e['app']['fn'],d-1)} {pp(e['app']['arg'],d-1)})"
    if "lam" in e: return f"(λ {pp(e['lam']['type'],2)}. {pp(e['lam']['body'],d-1)})"
    if "forallE" in e: return f"(Π {pp(e['forallE']['type'],2)}. {pp(e['forallE']['body'],d-1)})"
    if "natVal" in e: return str(e["natVal"])
    if "proj" in e: return f"proj{e['proj']['idx']} {pp(e['proj']['struct'],d-1)}"
    return str([k for k in e if k!='ie'])
for n in want:
    if n not in decls: print(n,"MISSING"); continue
    k,o=decls[n]
    print(n,k,o.get("hints"),"\n  ",pp(o["value"],16) if "value" in o else "")
