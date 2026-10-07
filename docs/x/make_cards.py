from PIL import Image, ImageDraw, ImageFont
import re, glob
W,H=3200,1800
BG=(11,15,23); FG=(230,237,243); MUTED=(159,179,200); BOX=(17,24,38); BORDER=(34,48,73)
KW=(122,162,247); CM=(107,122,144); AX=(247,118,142); OK=(158,206,106); VD=(224,175,104); AR=(92,107,130)
F='/System/Library/Fonts/Helvetica.ttc'; M='/System/Library/Fonts/Menlo.ttc'
def font(n,s): return ImageFont.truetype(n,s)
TITLE=font(F,84); SUB=font(F,48); NOTE=font(F,44); FOOT=font(F,40); MONO=font(M,46)
KWS={'theorem','lemma','def','noncomputable','instance','namespace','open','import','variable','by','fun','if','then','else','let','have','show','exact','intro','obtain','rw','simp','omega','calc','at','in','Type*','Type','Prop','∀','∃'}
def arrow(d,x1,y1,x2,y2):
    d.line([x1,y1,x2,y2],fill=AR,width=5)
    import math
    a=math.atan2(y2-y1,x2-x1); L=22
    p1=(x2-L*math.cos(a-0.5),y2-L*math.sin(a-0.5)); p2=(x2-L*math.cos(a+0.5),y2-L*math.sin(a+0.5))
    d.polygon([(x2,y2),p1,p2],fill=AR)
def draw_code(d,x,y,w,code,f=MONO):
    lines=code.split('\n'); lh=f.size*1.42; h=int(lh*len(lines)+90)
    d.rounded_rectangle([x,y,x+w,y+h],radius=28,fill=BOX,outline=BORDER,width=3)
    cy=y+45
    for line in lines:
        cx=x+50
        if line.strip().startswith('--'): d.text((cx,cy),line,font=f,fill=CM)
        else:
            for tok in re.findall(r'\s+|[A-Za-z_][\w.\'*]*|.',line):
                col=KW if tok in KWS else AX if tok in ('propext','Classical.choice','Quot.sound') else FG
                d.text((cx,cy),tok,font=f,fill=col); cx+=d.textlength(tok,font=f)
        cy+=lh
    return y+h
def wrap(d,text,f,w):
    lines=[];cur=''
    for wd in text.split(' '):
        t=(cur+' '+wd).strip()
        if d.textlength(t,font=f)<=w: cur=t
        else: lines.append(cur); cur=wd
    return lines+[cur]
def finish(im,d,y,footl,name):
    d.text((144,y+60),footl,font=FOOT,fill=MUTED)
    r=d.textlength('github.com/keithadler/saxl-lean',font=FOOT); d.text((W-144-r,y+60),'github.com/keithadler/saxl-lean',font=FOOT,fill=FG)
    h=y+170; out=im.crop((0,0,W,h))
    if h<W//2:
        o2=Image.new('RGB',(W,W//2),BG); o2.paste(out,(0,(W//2-h)//2)); out=o2
    out.save(name+'.png'); print(name,out.size)
def card(name,title,sub,code,note,footl):
    im=Image.new('RGB',(W,H),BG); d=ImageDraw.Draw(im)
    d.text((144,120),title,font=TITLE,fill=FG); d.text((144,230),sub,font=SUB,fill=MUTED)
    y=draw_code(d,144,330,W-288,code)+40
    for ln in wrap(d,note,NOTE,W-288): d.text((144,y),ln,font=NOTE,fill=(200,211,223)); y+=62
    finish(im,d,y,footl,name)
card('1_statement',"Saxl's conjecture, verified for staircases up to size 10",
 "Lean 4 + Mathlib, stated against OpenAI's own challenge file (verbatim)",
"""theorem saxl_le4 (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (μ : YoungDiagram) (hμ : μ.card = (staircase m).card) :
    0 < kronecker (canonicalTableau (staircase m) rfl)
                  (canonicalTableau (staircase m) rfl)
                  (canonicalTableau μ hμ)

#print axioms OAI.Saxl.saxl_le4
-- 'OAI.Saxl.saxl_le4' depends on axioms: [propext, Classical.choice, Quot.sound]""",
 "Every irreducible representation of S₁, S₃, S₆ and S₁₀ occurs in the tensor square of the staircase Specht module. kronecker is the dimension of the intertwiner space, exactly as the challenge defines it.",
 "Saxl/Thm31Small.lean · own proof, no vendored code")
card('2_classification',"Every irreducible representation of S_n is a Specht module",
 "The step the paper uses silently — proved by counting, no Wedderburn–Artin",
"""theorem exists_specht_occurs {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Perm (Fin n)) V)
    [ρ.IsIrreducible] :
    ∃ (η : YoungDiagram) (hη : η.card = n), Occurs (canonicalTableau η hη) ρ

-- idea: characters of ρ and of all S^η are linearly independent class
-- functions (char_orthonormal); S^η ≇ S^θ for η ≠ θ (dominance both ways);
-- conjugacy classes of S_n inject into Young diagrams ⇒ one function too many.""",
 "Two general ingredients were missing from Mathlib and are now submitted: irreducibles are bounded by conjugacy classes for any finite group (#44613), and conjugacy classes of S_n correspond to partitions (#44612).",
 "Saxl/Classification.lean · SpechtDistinct.lean · ClassDiagram.lean")
card('4_mathlib',"Upstreamed to Mathlib: the two general pieces",
 "Pull requests #44612 and #44613 — CI green, under review",
"""-- #44613  Mathlib/RepresentationTheory/CharacterCount.lean
theorem card_le_card_conjClasses [Fintype ι]
    (h : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) :
    Fintype.card ι ≤ Nat.card (ConjClasses G)
-- any finite group G, any algebraically closed k with |G| invertible

-- #44612  Mathlib/GroupTheory/Perm/ConjClassesPartition.lean
noncomputable def conjClassesEquivPartition :
    ConjClasses (Perm α) ≃ (Fintype.card α).Partition""",
 "Mathlib had character orthogonality but stopped short of the count, and had Perm.partition without the bijection. Both PRs are small, import-neutral and written to Mathlib style against master.",
 "leanprover-community/mathlib4 · PRs #44612, #44613")
# map
im=Image.new('RGB',(W,H),BG); d=ImageDraw.Draw(im)
d.text((144,120),"Proof map: from the paper to Lean",font=TITLE,fill=FG)
d.ellipse([144,248,180,284],fill=OK); d.text((200,230),"own proof (8,200 lines)",font=SUB,fill=MUTED)
x=200+d.textlength("own proof (8,200 lines)",font=SUB)+80
d.ellipse([x,248,x+36,284],outline=VD,width=5); d.pieslice([x,248,x+36,284],90,270,fill=VD)
d.text((x+56,230),"closed via OpenAI's vendored proof (7,800 lines, Apache-2.0)",font=SUB,fill=MUTED)
chain=[("Specht modules","polytabloids, column group"),("James's theorem","S^λ irreducible"),("Pieri rule","strip tableaux + Frobenius"),
 ("Sector lemma","Lemma 4.1, Ind without Ind"),("Young's rule","occurrence form"),("Prop 3.2","dominance base case"),
 ("Strip reduction","Lemma 6.1"),("Band cut, s = 1","Prop 4.2, width one"),("Theorem 3.1, m ≤ 4","induction closes"),
 ("Classification","irreducibles of S_n"),("Band cut, s = 2","margin, rotation, factorisation"),("Case (ii), m ≥ 5","vendored from OpenAI")]
BF=font(F,46); SF=font(F,34); cols=4; bw=680; bh=170; gx=(W-288-cols*bw)//(cols-1); x0=144; y0=360
for i,(t,s) in enumerate(chain):
    r,c=divmod(i,cols); x=x0+c*(bw+gx); y=y0+r*(bh+70)
    d.rounded_rectangle([x,y,x+bw,y+bh],radius=22,fill=BOX,outline=BORDER,width=3)
    vd='vendored' in s
    if vd: d.ellipse([x+30,y+48,x+66,y+84],outline=VD,width=5); d.pieslice([x+30,y+48,x+66,y+84],90,270,fill=VD)
    else: d.ellipse([x+30,y+48,x+66,y+84],fill=OK)
    d.text((x+90,y+34),t,font=BF,fill=FG); d.text((x+90,y+100),s,font=SF,fill=MUTED)
    if c<cols-1: arrow(d,x+bw+14,y+bh//2,x+bw+gx-14,y+bh//2)
    elif r<2: arrow(d,x+bw-60,y+bh+10,x+bw-60,y+bh+60)
y=y0+3*(bh+70)+10
for ln in wrap(d,"Every theorem axiom-checked: propext, Classical.choice, Quot.sound only. The README's Provenance table says exactly which file is whose; delete Saxl/OAI/ and everything on the green path still builds.",NOTE,W-288):
    d.text((144,y),ln,font=NOTE,fill=(200,211,223)); y+=62
finish(im,d,y,"38 own modules · 430 theorems · Lean v4.34.1 · Mathlib pinned to openai/math",'3_map')
