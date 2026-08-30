import RequestProject.TaoFramework

/-!
# 道德經 上篇 — Tao Te Ching, Book One (Chapters 1–37)

Each chapter is a `Prop`-valued statement about an abstract `Cosmos` (see
`TaoFramework.lean`).  The English translation in each docstring is the source of
the formalization; the encoding captures the principal logical claims of the
chapter using the primitive terms and relations of the framework.  Because the
text is poetic, the rendering is necessarily an approximation.
-/

namespace TaoTeChing
namespace Cosmos

variable (W : Cosmos)

local notation:max "⟦" c "⟧" => Cosmos.den W c

/-- **Chapter 1.** The way that can be stated is not the eternal way; the name
that can be named is not the eternal name. The unnamed is the origin of heaven
and earth; the named is the mother of the myriad things. The two share an origin
but differ in name; both are called Mystery — the gate to all wonders. -/
def chapter1 : Prop :=
  W.Eternal ⟦.dao⟧ ∧ W.Eternal ⟦.name⟧ ∧
  (∀ x, W.Speakable x → W.IsNot x ⟦.dao⟧) ∧
  (∀ x, W.Nameable x → W.IsNot x ⟦.name⟧) ∧
  W.OriginOf ⟦.nonBeing⟧ ⟦.heaven⟧ ∧ W.OriginOf ⟦.nonBeing⟧ ⟦.earth⟧ ∧
  W.MotherOf ⟦.being⟧ ⟦.myriad⟧ ∧
  (∃ o, W.OriginOf o ⟦.being⟧ ∧ W.OriginOf o ⟦.nonBeing⟧) ∧
  W.Is ⟦.being⟧ ⟦.mystery⟧ ∧ W.Is ⟦.nonBeing⟧ ⟦.mystery⟧ ∧
  W.Is ⟦.mystery⟧ ⟦.gate⟧ ∧ W.OriginOf ⟦.gate⟧ ⟦.wonder⟧

/-- **Chapter 2.** Beauty is known only because of ugliness; goodness only
because of evil. Being and nothing, hard and easy, long and short, high and low,
music and voice, front and back arise from one another. Hence the sage acts
without action, teaches without words, lets the myriad things arise without
claiming them, and because he takes no credit the credit does not depart. -/
def chapter2 : Prop :=
  W.Complements ⟦.beauty⟧ ⟦.ugliness⟧ ∧
  W.Complements ⟦.good⟧ ⟦.evil⟧ ∧
  W.Complements ⟦.being⟧ ⟦.nonBeing⟧ ∧
  W.Complements ⟦.difficult⟧ ⟦.easy⟧ ∧
  W.Complements ⟦.long⟧ ⟦.short⟧ ∧
  W.Complements ⟦.high⟧ ⟦.low⟧ ∧
  W.Complements ⟦.music⟧ ⟦.voice⟧ ∧
  W.Complements ⟦.front⟧ ⟦.back⟧ ∧
  W.Practices ⟦.sage⟧ ⟦.nonAction⟧ ∧
  W.Produces ⟦.sage⟧ ⟦.myriad⟧ ∧ ¬ W.Possesses ⟦.sage⟧ ⟦.myriad⟧ ∧
  ¬ W.Dwells ⟦.sage⟧ ⟦.credit⟧

/-- **Chapter 3.** Not exalting the worthy keeps people from rivalry; not prizing
rare goods keeps them from theft; not displaying desirables keeps minds calm.
The sage empties minds, fills bellies, weakens wills, strengthens bones, keeps
the people without knowledge and without desire — acting by non-action, nothing
is left ungoverned. -/
def chapter3 : Prop :=
  (¬ W.Dwells ⟦.ruler⟧ ⟦.worthy⟧ → ¬ W.Contends ⟦.people⟧) ∧
  (¬ W.Possesses ⟦.ruler⟧ ⟦.goods⟧ → ¬ W.Is ⟦.people⟧ ⟦.thief⟧) ∧
  (¬ W.Possesses ⟦.people⟧ ⟦.knowledge⟧ ∧ ¬ W.Possesses ⟦.people⟧ ⟦.desire⟧) ∧
  W.Practices ⟦.sage⟧ ⟦.nonAction⟧ ∧
  (W.Practices ⟦.sage⟧ ⟦.nonAction⟧ → ¬ ∃ x, W.IsNot x ⟦.governance⟧)

/-- **Chapter 4.** The Dao is empty, yet inexhaustible in use; profound, like the
ancestor of the myriad things. It blunts sharpness, unravels complexity,
harmonizes its light, mixes with the dust. Dim, it seems to exist. I know not
whose child it is; it seems to precede the Creator. -/
def chapter4 : Prop :=
  W.Empty ⟦.dao⟧ ∧
  W.OriginOf ⟦.dao⟧ ⟦.myriad⟧ ∧
  W.Resolves ⟦.dao⟧ ⟦.sharpness⟧ ∧
  W.Resolves ⟦.dao⟧ ⟦.complexity⟧ ∧
  W.Resolves ⟦.dao⟧ ⟦.light⟧ ∧
  W.Is ⟦.dao⟧ ⟦.dust⟧ ∧
  W.Exists_ ⟦.dao⟧ ∧
  W.Precedes ⟦.dao⟧ ⟦.heaven⟧

/-- **Chapter 5.** Heaven and earth are not benevolent; they treat the myriad
things as straw dogs. The sage is not benevolent; he treats the people as straw
dogs. The space between is like a bellows: empty yet inexhaustible, the more it
moves the more comes out. Many words exhaust; better to keep to the center. -/
def chapter5 : Prop :=
  ¬ W.Is ⟦.heaven⟧ ⟦.benevolence⟧ ∧
  W.Regards ⟦.heaven⟧ ⟦.myriad⟧ ⟦.strawDog⟧ ∧
  ¬ W.Is ⟦.sage⟧ ⟦.benevolence⟧ ∧
  W.Regards ⟦.sage⟧ ⟦.people⟧ ⟦.strawDog⟧ ∧
  W.IsLike ⟦.heaven⟧ ⟦.bellows⟧ ∧ W.Empty ⟦.bellows⟧ ∧
  W.BetterThan ⟦.stillness⟧ ⟦.voice⟧

/-- **Chapter 6.** The valley spirit never dies; it is the mysterious female.
The gate of the mysterious female is the root of heaven and earth. Continuous,
it seems to endure; used, it is never exhausted. -/
def chapter6 : Prop :=
  ¬ W.Fails ⟦.spirit⟧ ∧
  W.Is ⟦.spirit⟧ ⟦.female⟧ ∧
  W.Is ⟦.female⟧ ⟦.gate⟧ ∧
  W.OriginOf ⟦.gate⟧ ⟦.heaven⟧ ∧ W.OriginOf ⟦.gate⟧ ⟦.earth⟧ ∧
  W.Exists_ ⟦.spirit⟧ ∧ W.Endures ⟦.spirit⟧

/-- **Chapter 7.** Heaven and earth are eternal because they do not live for
themselves. Thus the sage puts himself last and yet comes first, places himself
outside and yet survives. Is it not because he is selfless that he fulfills
himself? -/
def chapter7 : Prop :=
  W.Eternal ⟦.heaven⟧ ∧ W.Eternal ⟦.earth⟧ ∧
  W.Precedes ⟦.sage⟧ ⟦.people⟧ ∧  -- putting himself behind, he nonetheless comes first
  W.Survives ⟦.sage⟧ ∧
  (¬ W.Possesses ⟦.sage⟧ ⟦.desire⟧ → W.Survives ⟦.sage⟧)

/-- **Chapter 8.** The highest good is like water, which benefits the myriad
things without contending and dwells where others disdain — thus close to the
Dao. Because it does not contend, it is without blame. -/
def chapter8 : Prop :=
  W.IsLike ⟦.good⟧ ⟦.water⟧ ∧
  W.Benefits ⟦.water⟧ ⟦.myriad⟧ ∧
  ¬ W.Contends ⟦.water⟧ ∧
  W.IsLike ⟦.water⟧ ⟦.dao⟧ ∧
  (¬ W.Contends ⟦.water⟧ → ¬ W.Is ⟦.water⟧ ⟦.blame⟧)

/-- **Chapter 9.** Better to stop than to overfill; a blade kept sharp will not
last; a hall full of gold and jade cannot be guarded; wealth and pride bring
their own ruin. To withdraw when the work is done is the way of heaven. -/
def chapter9 : Prop :=
  W.BetterThan ⟦.restraint⟧ ⟦.fullness⟧ ∧
  ¬ W.Endures ⟦.sharpness⟧ ∧
  (W.Possesses ⟦.ruler⟧ ⟦.wealth⟧ → W.Possesses ⟦.ruler⟧ ⟦.fault⟧) ∧
  W.Is ⟦.restraint⟧ ⟦.dao⟧

/-- **Chapter 10.** Can you keep body and soul embracing the One without
parting? Concentrate the breath to become as supple as an infant? Cleanse the
mind to be without flaw? Love the people and govern without cleverness? Produce
and nourish, produce without owning, act without claiming, lead without ruling —
this is called profound Virtue. -/
def chapter10 : Prop :=
  W.Dwells ⟦.sage⟧ ⟦.unity⟧ ∧
  W.IsLike ⟦.breath⟧ ⟦.infant⟧ ∧
  W.Loves ⟦.sage⟧ ⟦.people⟧ ∧
  ¬ W.Possesses ⟦.sage⟧ ⟦.knowledge⟧ ∧
  W.Produces ⟦.dao⟧ ⟦.myriad⟧ ∧ ¬ W.Possesses ⟦.dao⟧ ⟦.myriad⟧ ∧
  W.Nourishes ⟦.dao⟧ ⟦.myriad⟧ ∧
  W.Is ⟦.virtue⟧ ⟦.profound⟧

/-- **Chapter 11.** Thirty spokes share one hub: it is the emptiness at the
center that makes the cart useful. Clay forms a vessel, doors and windows a
room: it is their empty space that is of use. Thus being provides advantage,
while non-being provides usefulness. -/
def chapter11 : Prop :=
  W.OriginOf ⟦.emptiness⟧ ⟦.hub⟧ ∧
  W.OriginOf ⟦.emptiness⟧ ⟦.vessel⟧ ∧
  W.OriginOf ⟦.emptiness⟧ ⟦.room⟧ ∧
  W.Benefits ⟦.being⟧ ⟦.thing⟧ ∧
  W.Benefits ⟦.nonBeing⟧ ⟦.thing⟧ ∧
  W.Empty ⟦.nonBeing⟧

/-- **Chapter 12.** The five colors blind the eye, the five tones deafen the ear,
the five flavors numb the mouth, racing and hunting madden the heart, rare goods
impede right conduct. The sage tends to the belly, not the eye; he discards the
one and takes the other. -/
def chapter12 : Prop :=
  W.Harms ⟦.color⟧ ⟦.people⟧ ∧
  W.Harms ⟦.music⟧ ⟦.people⟧ ∧
  W.Harms ⟦.flavor⟧ ⟦.people⟧ ∧
  W.Harms ⟦.goods⟧ ⟦.people⟧ ∧
  W.Dwells ⟦.sage⟧ ⟦.belly⟧ ∧ ¬ W.Dwells ⟦.sage⟧ ⟦.color⟧

/-- **Chapter 13.** Favor and disgrace are both alarming; honor great trouble as
your own body. We have trouble because we have a body; without a body, what
trouble could we have? Therefore one who values the world as his own body may be
entrusted with the world. -/
def chapter13 : Prop :=
  W.IsLike ⟦.glory⟧ ⟦.fear⟧ ∧ W.IsLike ⟦.disgrace⟧ ⟦.fear⟧ ∧
  W.OriginOf ⟦.thing⟧ ⟦.fault⟧ ∧  -- having a body (a "thing") is the source of trouble
  (W.Regards ⟦.ruler⟧ ⟦.world⟧ ⟦.thing⟧ → W.Trusts ⟦.world⟧ ⟦.ruler⟧) ∧
  (W.Loves ⟦.ruler⟧ ⟦.world⟧ → W.Trusts ⟦.world⟧ ⟦.ruler⟧)

/-- **Chapter 14.** Looked at but unseen: the invisible. Listened to but unheard:
the soundless. Grasped but untouched: the intangible. These three merge into one.
It returns to no-thing — the shape without shape, the image without object. Hold
the ancient Dao to master the present: this is the thread of the Dao. -/
def chapter14 : Prop :=
  W.Is ⟦.invisible⟧ ⟦.dao⟧ ∧ W.Is ⟦.soundless⟧ ⟦.dao⟧ ∧ W.Is ⟦.intangible⟧ ⟦.dao⟧ ∧
  W.Is ⟦.dao⟧ ⟦.unity⟧ ∧
  W.Returns ⟦.dao⟧ ⟦.nonBeing⟧ ∧
  ¬ W.Nameable ⟦.dao⟧ ∧
  W.Is ⟦.dao⟧ ⟦.principle⟧

/-- **Chapter 15.** The ancient masters of the Dao were subtle and profound,
too deep to be known. Cautious, wary, grave, yielding, genuine like uncarved
wood, open like a valley, turbid like muddy water. Who can let the muddy settle
to clarity? Those who keep the Dao do not seek to be full, and so can be worn
yet renewed. -/
def chapter15 : Prop :=
  W.Knows ⟦.master⟧ ⟦.dao⟧ ∧ W.Is ⟦.master⟧ ⟦.profound⟧ ∧
  W.IsLike ⟦.master⟧ ⟦.winter⟧ ∧
  W.IsLike ⟦.master⟧ ⟦.wood⟧ ∧
  W.IsLike ⟦.master⟧ ⟦.valley⟧ ∧
  (W.Dwells ⟦.master⟧ ⟦.stillness⟧ → W.Transforms ⟦.master⟧ ⟦.clarity⟧) ∧
  ¬ W.Possesses ⟦.master⟧ ⟦.fullness⟧ ∧
  W.Is ⟦.master⟧ ⟦.freshness⟧

/-- **Chapter 16.** Attain utmost emptiness, hold firm to stillness. The myriad
things arise, and I watch them return. Each returns to its root; returning to the
root is stillness, which is returning to destiny. To know the eternal is
enlightenment; not to know it brings disaster. The eternal is all-embracing,
impartial, kingly, heavenly, the Dao, and enduring. -/
def chapter16 : Prop :=
  W.Returns ⟦.myriad⟧ ⟦.root⟧ ∧
  W.Is ⟦.root⟧ ⟦.stillness⟧ ∧
  W.Is ⟦.stillness⟧ ⟦.destiny⟧ ∧
  W.Is ⟦.destiny⟧ ⟦.eternal⟧ ∧
  (W.Knows ⟦.sage⟧ ⟦.eternal⟧ → W.Is ⟦.sage⟧ ⟦.enlightenment⟧) ∧
  (¬ W.Knows ⟦.sage⟧ ⟦.eternal⟧ → W.Is ⟦.sage⟧ ⟦.adversity⟧) ∧
  W.Is ⟦.eternal⟧ ⟦.dao⟧ ∧ W.Endures ⟦.dao⟧

/-- **Chapter 17.** The greatest ruler is barely known to the people; next, one
loved and praised; next, one feared; next, one despised. When trust is lacking,
there is no trust. The sage is sparing of words; when the work is done, the
people say it happened naturally. -/
def chapter17 : Prop :=
  W.BetterThan ⟦.ruler⟧ ⟦.king⟧ ∧
  (¬ W.Trusts ⟦.ruler⟧ ⟦.people⟧ → ¬ W.Trusts ⟦.people⟧ ⟦.ruler⟧) ∧
  (W.Is ⟦.achievement⟧ ⟦.completion⟧ → W.Is ⟦.achievement⟧ ⟦.nature⟧)

/-- **Chapter 18.** When the great Dao declines, benevolence and righteousness
appear. When cleverness and wisdom emerge, great hypocrisy arises. When family
relations break down, filial piety and affection appear. When the state falls
into disorder, loyal ministers appear. -/
def chapter18 : Prop :=
  (W.Fails ⟦.dao⟧ → W.Exists_ ⟦.benevolence⟧ ∧ W.Exists_ ⟦.righteousness⟧) ∧
  (W.Exists_ ⟦.wisdom⟧ → W.Exists_ ⟦.hypocrisy⟧) ∧
  (W.Fails ⟦.affection⟧ → W.Exists_ ⟦.filialPiety⟧) ∧
  (W.Fails ⟦.nation⟧ → W.Exists_ ⟦.loyalty⟧)

/-- **Chapter 19.** Abandon holiness and wisdom, and the people benefit a
hundredfold. Abandon benevolence and righteousness, and the people return to
filial piety and affection. Abandon cleverness and profit, and thieves
disappear. These three are not enough as doctrine; so hold to this: see
plainness, embrace simplicity, lessen self and reduce desire. -/
def chapter19 : Prop :=
  (W.Abandons ⟦.sage⟧ ⟦.wisdom⟧ → W.Benefits ⟦.dao⟧ ⟦.people⟧) ∧
  (W.Abandons ⟦.sage⟧ ⟦.benevolence⟧ → W.Returns ⟦.people⟧ ⟦.filialPiety⟧) ∧
  (W.Abandons ⟦.sage⟧ ⟦.cleverness⟧ → ¬ W.Exists_ ⟦.thief⟧) ∧
  W.Dwells ⟦.sage⟧ ⟦.simplicity⟧ ∧
  W.Reduces ⟦.sage⟧ ⟦.desire⟧

/-- **Chapter 20.** Abandon learning and be free of worry. How far apart are
flattery and reproach, good and evil? The crowd is merry as if at a feast; I
alone am still, like an infant not yet smiling. The crowd has plenty; I alone
seem to lack. I am a fool. I alone seek nourishment from the Mother. -/
def chapter20 : Prop :=
  (W.Abandons ⟦.sage⟧ ⟦.learning⟧ → ¬ W.Possesses ⟦.sage⟧ ⟦.anxiety⟧) ∧
  W.IsLike ⟦.sage⟧ ⟦.infant⟧ ∧
  W.Is ⟦.sage⟧ ⟦.fool⟧ ∧
  W.IsNot ⟦.sage⟧ ⟦.people⟧ ∧
  W.Nourishes ⟦.mother⟧ ⟦.sage⟧

/-- **Chapter 21.** The form of great Virtue follows only the Dao. The Dao as a
thing is elusive and vague, yet within it there is image, there is substance,
there is essence — and the essence is utterly real, holding truth. From of old
its name does not depart; through it we survey all beginnings. -/
def chapter21 : Prop :=
  W.Follows ⟦.virtue⟧ ⟦.dao⟧ ∧
  W.Possesses ⟦.dao⟧ ⟦.image⟧ ∧
  W.Possesses ⟦.dao⟧ ⟦.essence⟧ ∧
  W.Is ⟦.essence⟧ ⟦.faith⟧ ∧
  W.Eternal ⟦.name⟧

/-- **Chapter 22.** Yield and remain whole; bend and become straight; empty and
become full; worn out and become new. The sage embraces the One and is a model
for the world. He does not display himself, so he is bright; does not assert
himself, so he stands out. Because he does not contend, none can contend with
him. -/
def chapter22 : Prop :=
  W.IsLike ⟦.crooked⟧ ⟦.whole⟧ ∧
  W.IsLike ⟦.deficient⟧ ⟦.fullness⟧ ∧
  W.Dwells ⟦.sage⟧ ⟦.unity⟧ ∧
  W.Is ⟦.sage⟧ ⟦.example⟧ ∧
  ¬ W.Contends ⟦.sage⟧ ∧
  (¬ W.Contends ⟦.sage⟧ → ¬ ∃ x, W.Overcomes x ⟦.sage⟧)

/-- **Chapter 23.** Few words are natural. A whirlwind does not last a morning,
a downpour not a day. If heaven and earth cannot make these last, how much less
can man? One who follows the Dao becomes one with the Dao; one with Virtue, with
Virtue; one with loss, with loss. -/
def chapter23 : Prop :=
  W.Is ⟦.soundless⟧ ⟦.nature⟧ ∧
  ¬ W.Endures ⟦.motion⟧ ∧
  (¬ W.Endures ⟦.heaven⟧ → ¬ W.Endures ⟦.people⟧) ∧
  (W.Follows ⟦.people⟧ ⟦.dao⟧ → W.Is ⟦.people⟧ ⟦.dao⟧) ∧
  (W.Follows ⟦.people⟧ ⟦.virtue⟧ → W.Is ⟦.people⟧ ⟦.virtue⟧)

/-- **Chapter 24.** One on tiptoe does not stand; one who strides does not walk;
one who displays himself is not bright; one who is self-righteous is not
distinguished; one who boasts has no merit; one who is proud does not endure.
To the Dao these are excess and waste, which creatures dislike; so one with the
Dao does not dwell in them. -/
def chapter24 : Prop :=
  (W.Dwells ⟦.people⟧ ⟦.pride⟧ → ¬ W.Endures ⟦.people⟧) ∧
  (W.Dwells ⟦.people⟧ ⟦.pride⟧ → ¬ W.Possesses ⟦.people⟧ ⟦.achievement⟧) ∧
  W.IsLike ⟦.pride⟧ ⟦.surface⟧ ∧
  ¬ W.Dwells ⟦.sage⟧ ⟦.pride⟧

/-- **Chapter 25.** There is a thing formed in chaos, born before heaven and
earth. Silent and void, it stands alone unchanging, moves in cycles
untiring — the mother of the world. I call it the Dao, and, forced to name it,
great. Man follows earth, earth follows heaven, heaven follows the Dao, the Dao
follows nature. -/
def chapter25 : Prop :=
  W.Precedes ⟦.dao⟧ ⟦.heaven⟧ ∧ W.Precedes ⟦.dao⟧ ⟦.earth⟧ ∧
  W.MotherOf ⟦.dao⟧ ⟦.world⟧ ∧
  W.Is ⟦.dao⟧ ⟦.great⟧ ∧
  W.Follows ⟦.people⟧ ⟦.earth⟧ ∧
  W.Follows ⟦.earth⟧ ⟦.heaven⟧ ∧
  W.Follows ⟦.heaven⟧ ⟦.dao⟧ ∧
  W.Follows ⟦.dao⟧ ⟦.nature⟧

/-- **Chapter 26.** Heaviness is the root of lightness; stillness is the master
of restlessness. Hence the sage does not part from his baggage on a journey.
Why should a lord of ten thousand chariots treat himself lightly before the
world? Lightness loses the root; restlessness loses mastery. -/
def chapter26 : Prop :=
  W.OriginOf ⟦.heavy⟧ ⟦.lightWeight⟧ ∧
  W.Overcomes ⟦.stillness⟧ ⟦.restless⟧ ∧
  (W.Is ⟦.ruler⟧ ⟦.lightWeight⟧ → ¬ W.Dwells ⟦.ruler⟧ ⟦.root⟧) ∧
  (W.Is ⟦.ruler⟧ ⟦.restless⟧ → W.Fails ⟦.ruler⟧)

/-- **Chapter 27.** Good travel leaves no tracks; good speech no flaw; good
reckoning no counters; good shutting no bolt yet cannot be opened; good binding
no cord yet cannot be loosed. The sage always saves people, abandoning none, and
always saves things, abandoning none — this is hidden illumination. The good are
teachers of the bad; the bad are material for the good. -/
def chapter27 : Prop :=
  W.Saves ⟦.sage⟧ ⟦.people⟧ ∧ (∀ x, W.Is x ⟦.people⟧ → ¬ W.Abandons ⟦.sage⟧ x) ∧
  W.Saves ⟦.sage⟧ ⟦.thing⟧ ∧
  W.Is ⟦.good⟧ ⟦.teacher⟧ ∧
  W.Is ⟦.evil⟧ ⟦.resource⟧

/-- **Chapter 28.** Know the male but keep to the female, becoming the ravine of
the world; then constant Virtue does not leave, and you return to infancy. Know
the white but keep to the black, becoming the model of the world; then return to
the limitless. The uncarved block, when split, becomes vessels; the sage uses it
to become chief of officials. The great carver does not cut. -/
def chapter28 : Prop :=
  (W.Knows ⟦.sage⟧ ⟦.male⟧ ∧ W.Dwells ⟦.sage⟧ ⟦.female⟧) ∧
  W.Returns ⟦.sage⟧ ⟦.infant⟧ ∧
  (W.Knows ⟦.sage⟧ ⟦.white⟧ ∧ W.Dwells ⟦.sage⟧ ⟦.black⟧) ∧
  W.Returns ⟦.sage⟧ ⟦.limitless⟧ ∧
  (W.Knows ⟦.sage⟧ ⟦.glory⟧ ∧ W.Dwells ⟦.sage⟧ ⟦.disgrace⟧) ∧
  W.Returns ⟦.sage⟧ ⟦.simplicity⟧

/-- **Chapter 29.** Those who would seize the world and act on it will fail.
The world is a sacred vessel that cannot be acted upon; whoever acts on it ruins
it, whoever grasps it loses it. Things lead or follow, are strong or weak. Hence
the sage discards extremes, excess, and extravagance. -/
def chapter29 : Prop :=
  W.Is ⟦.world⟧ ⟦.vessel⟧ ∧
  (W.Acts ⟦.ruler⟧ → W.Fails ⟦.ruler⟧) ∧
  (W.Possesses ⟦.ruler⟧ ⟦.world⟧ → ¬ W.Possesses ⟦.ruler⟧ ⟦.world⟧) ∧
  W.Abandons ⟦.sage⟧ ⟦.pride⟧

/-- **Chapter 30.** One who assists a ruler with the Dao does not use arms to
dominate the world, for such things recoil. Where armies camp, thorns grow;
after great wars come years of famine. The good achieve their aim and stop, not
daring to take by force. What is grown strong grows old; this is against the Dao,
and what is against the Dao comes to an early end. -/
def chapter30 : Prop :=
  ¬ W.Dwells ⟦.dao⟧ ⟦.weapon⟧ ∧
  W.Harms ⟦.war⟧ ⟦.nation⟧ ∧
  (W.Is ⟦.good⟧ ⟦.achievement⟧ ∧ ¬ W.Possesses ⟦.good⟧ ⟦.pride⟧) ∧
  (W.Is ⟦.strong⟧ ⟦.death⟧) ∧
  (W.IsNot ⟦.strong⟧ ⟦.dao⟧ → W.Fails ⟦.strong⟧)

/-- **Chapter 31.** Fine weapons are instruments of ill omen, hated by all, so
one with the Dao does not dwell with them. They are not the gentleman's tools;
used only when unavoidable, with calm and restraint. To delight in victory is to
delight in killing, and one who delights in killing cannot win the world.
Therefore a battle is treated as a funeral. -/
def chapter31 : Prop :=
  W.Is ⟦.weapon⟧ ⟦.inauspicious⟧ ∧
  ¬ W.Dwells ⟦.dao⟧ ⟦.weapon⟧ ∧
  (W.Loves ⟦.ruler⟧ ⟦.victory⟧ → ¬ W.Conquers ⟦.ruler⟧ ⟦.world⟧) ∧
  W.Is ⟦.war⟧ ⟦.mourning⟧

/-- **Chapter 32.** The Dao is eternally nameless. Though the uncarved block is
small, none in the world can subordinate it. If rulers could keep to it, the
myriad things would submit of themselves, heaven and earth would unite to send
sweet dew, and the people would order themselves without command. Once there are
names, know when to stop; knowing when to stop averts danger. -/
def chapter32 : Prop :=
  ¬ W.Nameable ⟦.dao⟧ ∧
  W.Eternal ⟦.dao⟧ ∧
  (W.Dwells ⟦.ruler⟧ ⟦.dao⟧ → W.Follows ⟦.myriad⟧ ⟦.dao⟧) ∧
  (W.Dwells ⟦.ruler⟧ ⟦.restraint⟧ → ¬ W.Fails ⟦.ruler⟧) ∧
  W.IsLike ⟦.dao⟧ ⟦.ocean⟧

/-- **Chapter 33.** Knowing others is wisdom; knowing oneself is enlightenment.
Overcoming others is strength; overcoming oneself is true power. The contented
are rich; the persevering have will; those who do not lose their place endure;
those who die but are not forgotten have long life. -/
def chapter33 : Prop :=
  (W.Knows ⟦.sage⟧ ⟦.people⟧ → W.Is ⟦.sage⟧ ⟦.wisdom⟧) ∧
  (W.Knows ⟦.sage⟧ ⟦.sage⟧ → W.Is ⟦.sage⟧ ⟦.enlightenment⟧) ∧
  (W.Overcomes ⟦.sage⟧ ⟦.sage⟧ → W.Is ⟦.sage⟧ ⟦.strong⟧) ∧
  (W.Possesses ⟦.sage⟧ ⟦.contentment⟧ → W.Is ⟦.sage⟧ ⟦.wealth⟧) ∧
  (¬ W.Fails ⟦.sage⟧ → W.Endures ⟦.sage⟧)

/-- **Chapter 34.** The great Dao flows everywhere, left and right. The myriad
things depend on it for life and it does not refuse them; it accomplishes its
work without claiming it. It clothes and nourishes all without lordship — being
without desire, it may be called small; all things return to it without lordship,
so it may be called great. Because the sage never strives for greatness, he
achieves greatness. -/
def chapter34 : Prop :=
  W.GivesBirthTo ⟦.dao⟧ ⟦.myriad⟧ ∧
  ¬ W.Possesses ⟦.dao⟧ ⟦.myriad⟧ ∧
  ¬ W.Possesses ⟦.dao⟧ ⟦.desire⟧ ∧
  W.Is ⟦.dao⟧ ⟦.small⟧ ∧
  W.Returns ⟦.myriad⟧ ⟦.dao⟧ ∧
  W.Is ⟦.dao⟧ ⟦.great⟧ ∧
  (¬ W.Acts ⟦.sage⟧ → W.Is ⟦.sage⟧ ⟦.great⟧)

/-- **Chapter 35.** Hold the great image and the world comes to you; coming, it
is unharmed, at peace and secure. Music and food make the passer-by stop, but
the Dao, when spoken, is bland and flavorless — looked at, unseen; listened to,
unheard; used, inexhaustible. -/
def chapter35 : Prop :=
  (W.Dwells ⟦.ruler⟧ ⟦.image⟧ → W.Follows ⟦.world⟧ ⟦.ruler⟧) ∧
  ¬ W.Harms ⟦.image⟧ ⟦.world⟧ ∧
  W.Is ⟦.world⟧ ⟦.peace⟧ ∧
  ¬ W.Speakable ⟦.dao⟧ ∧
  W.Empty ⟦.dao⟧

/-- **Chapter 36.** To shrink something, first expand it; to weaken, first
strengthen; to discard, first promote; to take, first give. This is subtle
insight. The soft overcomes the hard, the weak the strong. Fish cannot leave the
deep; a state's sharp weapons should not be shown to others. -/
def chapter36 : Prop :=
  W.Overcomes ⟦.soft⟧ ⟦.hard⟧ ∧
  W.Overcomes ⟦.weak⟧ ⟦.strong⟧ ∧
  ¬ W.Dwells ⟦.fish⟧ ⟦.surface⟧ ∧
  ¬ W.Speakable ⟦.weapon⟧

/-- **Chapter 37.** The Dao does nothing, yet nothing is left undone. If rulers
could keep to it, the myriad things would transform of themselves; should desire
arise, I would still it with nameless simplicity. Nameless simplicity is freedom
from desire; without desire there is stillness, and the world settles itself. -/
def chapter37 : Prop :=
  ¬ W.Acts ⟦.dao⟧ ∧
  (¬ W.Acts ⟦.dao⟧ → ¬ ∃ x, W.IsNot x ⟦.completion⟧) ∧
  (W.Dwells ⟦.ruler⟧ ⟦.dao⟧ → W.Transforms ⟦.myriad⟧ ⟦.nature⟧) ∧
  W.Resolves ⟦.simplicity⟧ ⟦.desire⟧ ∧
  (W.Dwells ⟦.world⟧ ⟦.stillness⟧ → W.Is ⟦.world⟧ ⟦.straight⟧)

end Cosmos
end TaoTeChing
