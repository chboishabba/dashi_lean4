import RequestProject.TaoFramework
import RequestProject.TaoShang

/-!
# 道德經 下篇 — Tao Te Ching, Book Two (Chapters 38–81)

Each chapter is a `Prop`-valued statement about an abstract `Cosmos` (see
`TaoFramework.lean`).  The English translation in each docstring is the source of
the formalization.
-/

namespace TaoTeChing
namespace Cosmos

variable (W : Cosmos)

local notation:max "⟦" c "⟧" => Cosmos.den W c

/-- **Chapter 38.** Superior Virtue does not strive to be virtuous, and so has
Virtue; inferior Virtue clings to virtue, and so lacks it. When the Dao is lost
there is Virtue; when Virtue is lost, benevolence; then righteousness; then
ritual — and ritual is the husk of loyalty and faith and the beginning of
disorder. The great man dwells in the substantial, not the superficial. -/
def chapter38 : Prop :=
  (¬ W.Acts ⟦.virtue⟧ → W.Possesses ⟦.virtue⟧ ⟦.virtue⟧) ∧
  (W.Fails ⟦.dao⟧ → W.Exists_ ⟦.virtue⟧) ∧
  (W.Fails ⟦.virtue⟧ → W.Exists_ ⟦.benevolence⟧) ∧
  (W.Fails ⟦.benevolence⟧ → W.Exists_ ⟦.righteousness⟧) ∧
  (W.Fails ⟦.righteousness⟧ → W.Exists_ ⟦.ritual⟧) ∧
  W.OriginOf ⟦.ritual⟧ ⟦.complexity⟧ ∧
  W.Dwells ⟦.master⟧ ⟦.depth⟧ ∧ ¬ W.Dwells ⟦.master⟧ ⟦.surface⟧

/-- **Chapter 39.** Of old, those that attained the One: heaven became clear,
earth firm, the spirit serene, the valley full, the myriad things alive, rulers
upright. Without it heaven would crack, earth quake, the spirit cease, the valley
dry, things perish, rulers fall. Thus the noble takes the humble as its root,
the high takes the low as its foundation. Better to be plain like stone than
glittering like jade. -/
def chapter39 : Prop :=
  (W.Dwells ⟦.heaven⟧ ⟦.unity⟧ → W.Is ⟦.heaven⟧ ⟦.clarity⟧) ∧
  (W.Dwells ⟦.earth⟧ ⟦.unity⟧ → W.Is ⟦.earth⟧ ⟦.peace⟧) ∧
  (W.Dwells ⟦.spirit⟧ ⟦.unity⟧ → W.Is ⟦.spirit⟧ ⟦.stillness⟧) ∧
  (W.Dwells ⟦.myriad⟧ ⟦.unity⟧ → W.Exists_ ⟦.life⟧) ∧
  W.OriginOf ⟦.humility⟧ ⟦.dignity⟧ ∧
  W.OriginOf ⟦.low⟧ ⟦.high⟧ ∧
  W.BetterThan ⟦.stone⟧ ⟦.jade⟧

/-- **Chapter 40.** Returning is the movement of the Dao; weakness is its use.
The myriad things of the world are born of being, and being is born of
non-being. -/
def chapter40 : Prop :=
  W.Is ⟦.«return»⟧ ⟦.motion⟧ ∧
  W.Is ⟦.weak⟧ ⟦.dao⟧ ∧
  W.GivesBirthTo ⟦.being⟧ ⟦.myriad⟧ ∧
  W.GivesBirthTo ⟦.nonBeing⟧ ⟦.being⟧

/-- **Chapter 41.** The superior scholar, hearing the Dao, practices it; the
middling one half-believes; the inferior one laughs aloud — and without laughter
it would not be the Dao. Thus: the bright Dao seems dim, advance seems retreat,
great Virtue seems a valley, great whiteness seems disgraced, the great square
has no corners, the great vessel is completed late, the great sound is faint, the
great image has no form. The Dao alone gives and completes. -/
def chapter41 : Prop :=
  (W.Knows ⟦.scholar⟧ ⟦.dao⟧ → W.Practices ⟦.scholar⟧ ⟦.dao⟧) ∧
  W.IsLike ⟦.dao⟧ ⟦.invisible⟧ ∧
  W.IsLike ⟦.virtue⟧ ⟦.valley⟧ ∧
  W.IsLike ⟦.white⟧ ⟦.disgrace⟧ ∧
  W.IsLike ⟦.great⟧ ⟦.soundless⟧ ∧
  W.IsLike ⟦.image⟧ ⟦.invisible⟧ ∧
  W.Produces ⟦.dao⟧ ⟦.myriad⟧

/-- **Chapter 42.** The Dao gives birth to one, one to two, two to three, three
to the myriad things. The myriad things carry yin and embrace yang, blending the
breaths into harmony. Thus things gain by losing and lose by gaining. The
violent do not die a natural death — this I take as the heart of my teaching. -/
def chapter42 : Prop :=
  W.GivesBirthTo ⟦.dao⟧ ⟦.unity⟧ ∧
  W.GivesBirthTo ⟦.unity⟧ ⟦.two⟧ ∧
  W.GivesBirthTo ⟦.two⟧ ⟦.three⟧ ∧
  W.GivesBirthTo ⟦.three⟧ ⟦.myriad⟧ ∧
  W.Possesses ⟦.myriad⟧ ⟦.yin⟧ ∧ W.Possesses ⟦.myriad⟧ ⟦.yang⟧ ∧
  W.Is ⟦.breath⟧ ⟦.harmony⟧ ∧
  W.Fails ⟦.strong⟧

/-- **Chapter 43.** The softest in the world overruns the hardest; that which has
no substance enters where there is no space. Thus I know the value of
non-action. Teaching without words and the benefit of non-action — few in the
world attain them. -/
def chapter43 : Prop :=
  W.Overcomes ⟦.soft⟧ ⟦.hard⟧ ∧
  W.Benefits ⟦.nonAction⟧ ⟦.world⟧ ∧
  W.IsLike ⟦.soft⟧ ⟦.water⟧

/-- **Chapter 44.** Fame or self, which is dearer? Self or wealth, which is more?
Gain or loss, which is the worse ill? Excessive love brings great cost; great
hoarding brings heavy loss. Know contentment and avoid disgrace; know when to
stop and avoid danger — thus you may long endure. -/
def chapter44 : Prop :=
  (W.Loves ⟦.people⟧ ⟦.fame⟧ → W.Possesses ⟦.people⟧ ⟦.cost⟧) ∧
  (W.Possesses ⟦.people⟧ ⟦.hoard⟧ → W.Fails ⟦.people⟧) ∧
  (W.Possesses ⟦.people⟧ ⟦.contentment⟧ → ¬ W.Is ⟦.people⟧ ⟦.disgrace⟧) ∧
  (W.Dwells ⟦.people⟧ ⟦.restraint⟧ → W.Endures ⟦.people⟧)

/-- **Chapter 45.** Great completion seems deficient, yet its use never fails;
great fullness seems empty, yet its use is inexhaustible. Great straightness
seems bent, great skill seems clumsy, great eloquence seems halting. Motion
overcomes cold, stillness overcomes heat; purity and stillness set the world
right. -/
def chapter45 : Prop :=
  W.IsLike ⟦.completion⟧ ⟦.deficient⟧ ∧
  W.IsLike ⟦.fullness⟧ ⟦.emptiness⟧ ∧
  W.IsLike ⟦.straight⟧ ⟦.crooked⟧ ∧
  W.Overcomes ⟦.motion⟧ ⟦.cold⟧ ∧
  W.Overcomes ⟦.stillness⟧ ⟦.heat⟧ ∧
  W.Is ⟦.purity⟧ ⟦.straight⟧

/-- **Chapter 46.** When the world has the Dao, swift horses haul manure; when it
lacks the Dao, war-horses are bred at the frontier. No sin is greater than
desire, no fault greater than discontent, no calamity greater than greed.
Therefore one who knows that enough is enough always has enough. -/
def chapter46 : Prop :=
  (W.Dwells ⟦.world⟧ ⟦.dao⟧ → ¬ W.Exists_ ⟦.war⟧) ∧
  W.Is ⟦.desire⟧ ⟦.sin⟧ ∧
  W.Is ⟦.fault⟧ ⟦.desire⟧ ∧
  (W.Possesses ⟦.people⟧ ⟦.contentment⟧ → W.Endures ⟦.people⟧)

/-- **Chapter 47.** Without going out the door, one may know the world; without
looking out the window, one may see the Dao of heaven. The farther one goes, the
less one knows. Hence the sage knows without traveling, names without seeing,
accomplishes without acting. -/
def chapter47 : Prop :=
  W.Knows ⟦.sage⟧ ⟦.world⟧ ∧
  W.Knows ⟦.sage⟧ ⟦.dao⟧ ∧
  (W.Possesses ⟦.sage⟧ ⟦.journey⟧ → ¬ W.Knows ⟦.sage⟧ ⟦.world⟧) ∧
  (¬ W.Acts ⟦.sage⟧ → W.Is ⟦.achievement⟧ ⟦.completion⟧)

/-- **Chapter 48.** In pursuing learning, one gains daily; in pursuing the Dao,
one loses daily — losing and losing until one reaches non-action. Act not, and
nothing is left undone. The world is won by not meddling; one who meddles cannot
win the world. -/
def chapter48 : Prop :=
  (W.Practices ⟦.people⟧ ⟦.learning⟧ → W.Supplements ⟦.learning⟧ ⟦.people⟧) ∧
  (W.Practices ⟦.people⟧ ⟦.dao⟧ → W.Reduces ⟦.dao⟧ ⟦.people⟧) ∧
  (¬ W.Acts ⟦.sage⟧ → W.Conquers ⟦.sage⟧ ⟦.world⟧) ∧
  (W.Acts ⟦.ruler⟧ → ¬ W.Conquers ⟦.ruler⟧ ⟦.world⟧)

/-- **Chapter 49.** The sage has no fixed mind; he takes the people's mind as his
mind. To the good he is good, and to the bad he is also good — this is the
goodness of Virtue. The faithful he trusts, and the unfaithful he also trusts —
this is the faith of Virtue. The sage treats all the people as his children. -/
def chapter49 : Prop :=
  W.Is ⟦.people⟧ ⟦.mind⟧ ∧
  W.Is ⟦.good⟧ ⟦.virtue⟧ ∧
  W.Trusts ⟦.sage⟧ ⟦.people⟧ ∧
  W.Is ⟦.faith⟧ ⟦.virtue⟧ ∧
  W.Regards ⟦.sage⟧ ⟦.people⟧ ⟦.child⟧

/-- **Chapter 50.** Coming out into life and going back into death: three in ten
are companions of life, three in ten of death, and three in ten pass to the
ground of death through clinging to life. One who is good at preserving life
meets no tiger in the hills and no weapon in battle, for in him there is no
ground of death. -/
def chapter50 : Prop :=
  (W.Knows ⟦.sage⟧ ⟦.life⟧ → ¬ W.Harms ⟦.tiger⟧ ⟦.sage⟧) ∧
  (W.Knows ⟦.sage⟧ ⟦.life⟧ → ¬ W.Harms ⟦.weapon⟧ ⟦.sage⟧) ∧
  ¬ W.Dwells ⟦.sage⟧ ⟦.death⟧

/-- **Chapter 51.** The Dao gives birth, Virtue rears, matter shapes,
circumstance completes. Thus the myriad things all honor the Dao and value
Virtue — honor and value that are commanded by none but arise naturally. It
gives life without owning, acts without claiming, leads without ruling: this is
profound Virtue. -/
def chapter51 : Prop :=
  W.GivesBirthTo ⟦.dao⟧ ⟦.myriad⟧ ∧
  W.Nourishes ⟦.virtue⟧ ⟦.myriad⟧ ∧
  W.Follows ⟦.myriad⟧ ⟦.dao⟧ ∧
  W.Produces ⟦.dao⟧ ⟦.myriad⟧ ∧ ¬ W.Possesses ⟦.dao⟧ ⟦.myriad⟧ ∧
  W.Is ⟦.virtue⟧ ⟦.profound⟧

/-- **Chapter 52.** The world had a beginning, the mother of all. Knowing the
mother, one knows her children; knowing the children and keeping to the mother,
one is free from danger to the end. Block the openings, shut the gate, and you
will not toil all your life. Seeing the small is insight; keeping to softness is
strength. -/
def chapter52 : Prop :=
  W.MotherOf ⟦.origin⟧ ⟦.world⟧ ∧
  (W.Knows ⟦.sage⟧ ⟦.mother⟧ → W.Knows ⟦.sage⟧ ⟦.child⟧) ∧
  (W.Dwells ⟦.sage⟧ ⟦.mother⟧ → ¬ W.Fails ⟦.sage⟧) ∧
  W.Is ⟦.enlightenment⟧ ⟦.small⟧ ∧
  W.Is ⟦.strong⟧ ⟦.soft⟧

/-- **Chapter 53.** If I had the least knowledge, I would walk the great Way and
fear only to stray. The great Way is smooth, yet people love bypaths. When the
court is splendid while the fields are weeds and the granaries empty, when men
wear finery and carry sharp swords, gorge on food and hoard wealth — this is
robbery and bragging, not the Dao. -/
def chapter53 : Prop :=
  W.Is ⟦.dao⟧ ⟦.straight⟧ ∧
  W.Loves ⟦.people⟧ ⟦.path⟧ ∧
  W.Is ⟦.wealth⟧ ⟦.thief⟧ ∧
  W.IsNot ⟦.thief⟧ ⟦.dao⟧

/-- **Chapter 54.** What is well planted is not uprooted; what is well embraced
does not slip away; thus offerings continue for generations. Cultivated in the
self, Virtue becomes real; in the family, abundant; in the village, lasting; in
the state, rich; in the world, universal. Observe self by self, world by world.
How do I know the world? By this. -/
def chapter54 : Prop :=
  (W.Dwells ⟦.virtue⟧ ⟦.sage⟧ → W.Endures ⟦.virtue⟧) ∧
  (W.Dwells ⟦.virtue⟧ ⟦.nation⟧ → W.Is ⟦.virtue⟧ ⟦.fullness⟧) ∧
  (W.Dwells ⟦.virtue⟧ ⟦.world⟧ → W.Is ⟦.virtue⟧ ⟦.great⟧) ∧
  W.Knows ⟦.sage⟧ ⟦.world⟧

/-- **Chapter 55.** One full of Virtue is like a newborn: poisonous creatures do
not sting it, beasts do not seize it, birds of prey do not strike it. Its bones
are weak, its sinews soft, yet its grip is firm. Knowing harmony is the eternal;
knowing the eternal is enlightenment. What is grown strong grows old — this is
against the Dao, and what is against the Dao soon ends. -/
def chapter55 : Prop :=
  W.IsLike ⟦.virtue⟧ ⟦.infant⟧ ∧
  ¬ W.Harms ⟦.beast⟧ ⟦.infant⟧ ∧
  ¬ W.Harms ⟦.bird⟧ ⟦.infant⟧ ∧
  (W.Knows ⟦.sage⟧ ⟦.harmony⟧ → W.Is ⟦.sage⟧ ⟦.eternal⟧) ∧
  (W.Knows ⟦.sage⟧ ⟦.eternal⟧ → W.Is ⟦.sage⟧ ⟦.enlightenment⟧) ∧
  (W.IsNot ⟦.strong⟧ ⟦.dao⟧ → W.Fails ⟦.strong⟧)

/-- **Chapter 56.** Those who know do not speak; those who speak do not know.
Block the openings, shut the gate, blunt the sharpness, untie the tangles,
soften the light, merge with the dust — this is profound union. It cannot be
gained for love or hate, profit or harm, honor or disgrace; therefore it is
honored by the world. -/
def chapter56 : Prop :=
  (W.Knows ⟦.sage⟧ ⟦.dao⟧ → ¬ W.Speakable ⟦.sage⟧) ∧
  W.Resolves ⟦.sage⟧ ⟦.sharpness⟧ ∧
  W.Resolves ⟦.sage⟧ ⟦.complexity⟧ ∧
  W.Is ⟦.sage⟧ ⟦.mystery⟧ ∧
  (¬ W.Possesses ⟦.people⟧ ⟦.love⟧) ∧
  W.Dwells ⟦.world⟧ ⟦.dignity⟧

/-- **Chapter 57.** Govern the state by rectitude, wage war by surprise, win the
world by non-interference. The more taboos, the poorer the people; the more sharp
weapons, the more disordered the state; the more laws, the more thieves.
Therefore the sage says: I act not, and the people transform themselves; I love
stillness, and they become upright; I do not meddle, and they prosper; I am
without desire, and they become simple. -/
def chapter57 : Prop :=
  (W.Possesses ⟦.nation⟧ ⟦.taboo⟧ → ¬ W.Possesses ⟦.people⟧ ⟦.wealth⟧) ∧
  (W.Possesses ⟦.nation⟧ ⟦.law⟧ → W.Exists_ ⟦.thief⟧) ∧
  (¬ W.Acts ⟦.sage⟧ → W.Transforms ⟦.people⟧ ⟦.nature⟧) ∧
  (W.Dwells ⟦.sage⟧ ⟦.stillness⟧ → W.Is ⟦.people⟧ ⟦.straight⟧) ∧
  (¬ W.Possesses ⟦.sage⟧ ⟦.desire⟧ → W.Is ⟦.people⟧ ⟦.simplicity⟧)

/-- **Chapter 58.** When government is dull, people are honest; when government is
sharp, people are cunning. Calamity is where fortune leans; fortune is where
calamity hides. Who knows the limit? There is no norm. Hence the sage is square
without cutting, sharp without wounding, straight without overreaching, bright
without dazzling. -/
def chapter58 : Prop :=
  W.OriginOf ⟦.adversity⟧ ⟦.fortune⟧ ∧
  W.OriginOf ⟦.fortune⟧ ⟦.adversity⟧ ∧
  W.Transforms ⟦.straight⟧ ⟦.crooked⟧ ∧
  W.Is ⟦.sage⟧ ⟦.straight⟧ ∧ ¬ W.Harms ⟦.sage⟧ ⟦.people⟧

/-- **Chapter 59.** In governing men and serving heaven, nothing is like
frugality. Frugality means early submission; early submission means amassing
Virtue; with Virtue amassed, nothing is insurmountable, and one's limits are
unknown — then one may hold a state. With the Mother of the state, one may long
endure. This is deep roots and a firm stem, the Dao of long life and lasting
vision. -/
def chapter59 : Prop :=
  W.BetterThan ⟦.frugality⟧ ⟦.action⟧ ∧
  (W.Dwells ⟦.ruler⟧ ⟦.frugality⟧ → W.Possesses ⟦.ruler⟧ ⟦.virtue⟧) ∧
  (W.Possesses ⟦.ruler⟧ ⟦.virtue⟧ → W.Possesses ⟦.ruler⟧ ⟦.nation⟧) ∧
  (W.Dwells ⟦.ruler⟧ ⟦.root⟧ → W.Endures ⟦.ruler⟧)

/-- **Chapter 60.** Governing a great state is like cooking small fish. Approach
the world with the Dao, and evil spirits lose their power; not that they have no
power, but their power does not harm people. Since neither the spirits nor the
sage do harm, Virtue accrues to both. -/
def chapter60 : Prop :=
  W.IsLike ⟦.governance⟧ ⟦.fish⟧ ∧
  (W.Dwells ⟦.world⟧ ⟦.dao⟧ → ¬ W.Harms ⟦.spirit⟧ ⟦.people⟧) ∧
  ¬ W.Harms ⟦.sage⟧ ⟦.people⟧ ∧
  W.Returns ⟦.virtue⟧ ⟦.world⟧

/-- **Chapter 61.** A great state is a low-lying confluence, the female of the
world; the female overcomes the male through stillness, by lying low. So a great
state that lowers itself wins over a small state, and a small state that lowers
itself wins over a great. Both get what they want when the great lies low. -/
def chapter61 : Prop :=
  W.Is ⟦.nation⟧ ⟦.low⟧ ∧
  W.Is ⟦.nation⟧ ⟦.female⟧ ∧
  W.Overcomes ⟦.female⟧ ⟦.male⟧ ∧
  (W.Dwells ⟦.nation⟧ ⟦.low⟧ → W.Conquers ⟦.nation⟧ ⟦.nation⟧) ∧
  W.Dwells ⟦.nation⟧ ⟦.humility⟧

/-- **Chapter 62.** The Dao is the storehouse of all things, the treasure of the
good and the refuge of the bad. Fine words can buy honor, noble deeds can raise
a man; even the bad are not cast away. Thus when emperors are crowned and
ministers installed, better to sit and offer this Dao than present jade and
horses. Therefore the world treasures it. -/
def chapter62 : Prop :=
  W.Is ⟦.dao⟧ ⟦.treasure⟧ ∧
  W.Saves ⟦.dao⟧ ⟦.evil⟧ ∧
  W.BetterThan ⟦.dao⟧ ⟦.jade⟧ ∧
  W.Dwells ⟦.world⟧ ⟦.dao⟧ ∧
  W.Is ⟦.dao⟧ ⟦.dignity⟧

/-- **Chapter 63.** Act without acting, work without working, taste without
tasting. Repay injury with Virtue. Plan the difficult while it is easy, do the
great while it is small. The world's hard tasks begin easy, its great tasks
begin small; hence the sage never strives for greatness and so achieves it.
Light promises win little trust; the sage treats things as difficult, and so has
no difficulty. -/
def chapter63 : Prop :=
  W.Practices ⟦.sage⟧ ⟦.nonAction⟧ ∧
  W.Resolves ⟦.virtue⟧ ⟦.blame⟧ ∧
  W.OriginOf ⟦.easy⟧ ⟦.difficult⟧ ∧
  W.OriginOf ⟦.small⟧ ⟦.great⟧ ∧
  (¬ W.Acts ⟦.sage⟧ → W.Is ⟦.sage⟧ ⟦.great⟧) ∧
  ¬ W.Possesses ⟦.sage⟧ ⟦.difficult⟧

/-- **Chapter 64.** What is at rest is easy to hold, what has not begun is easy to
plan, what is brittle is easy to break, what is tiny is easy to scatter. Deal
with things before they arise. A great tree grows from a sprout, a tall tower
from a heap of earth, a long journey from a single step. Those who act ruin it;
those who grasp lose it; the sage acts not, and so fails not. -/
def chapter64 : Prop :=
  W.OriginOf ⟦.sprout⟧ ⟦.tree⟧ ∧
  W.OriginOf ⟦.mound⟧ ⟦.tower⟧ ∧
  W.OriginOf ⟦.step⟧ ⟦.journey⟧ ∧
  (W.Acts ⟦.ruler⟧ → W.Fails ⟦.ruler⟧) ∧
  (¬ W.Acts ⟦.sage⟧ → ¬ W.Fails ⟦.sage⟧) ∧
  W.Follows ⟦.sage⟧ ⟦.nature⟧

/-- **Chapter 65.** The ancient masters of the Dao did not enlighten the people
with it, but kept them simple. People are hard to govern because they have too
much cleverness; to govern with cleverness is to rob the state, to govern without
it is to bless the state. To know these two is the model — and knowing the model
is profound Virtue, deep and far-reaching, returning with all things to the great
accord. -/
def chapter65 : Prop :=
  (W.Knows ⟦.master⟧ ⟦.dao⟧ → W.Is ⟦.people⟧ ⟦.simplicity⟧) ∧
  (W.Dwells ⟦.ruler⟧ ⟦.cleverness⟧ → W.Harms ⟦.ruler⟧ ⟦.nation⟧) ∧
  (¬ W.Dwells ⟦.ruler⟧ ⟦.cleverness⟧ → W.Benefits ⟦.ruler⟧ ⟦.nation⟧) ∧
  W.Is ⟦.virtue⟧ ⟦.profound⟧ ∧
  W.Returns ⟦.virtue⟧ ⟦.harmony⟧

/-- **Chapter 66.** Rivers and seas are kings of the hundred valleys because they
lie below them. Hence to be above the people, the sage speaks humbly of himself;
to lead them, he puts himself behind. So he is above without burdening, ahead
without harming; the world delights to push him forward without tiring. Because
he does not contend, none can contend with him. -/
def chapter66 : Prop :=
  W.OriginOf ⟦.low⟧ ⟦.king⟧ ∧
  W.Dwells ⟦.ocean⟧ ⟦.low⟧ ∧
  W.Precedes ⟦.sage⟧ ⟦.people⟧ ∧ ¬ W.Harms ⟦.sage⟧ ⟦.people⟧ ∧
  ¬ W.Contends ⟦.sage⟧ ∧
  (¬ W.Contends ⟦.sage⟧ → ¬ ∃ x, W.Overcomes x ⟦.sage⟧)

/-- **Chapter 67.** I have three treasures I hold and keep: mercy, frugality, and
not daring to be first in the world. From mercy comes courage, from frugality
comes generosity, from not daring to be first comes the capacity to lead. To
abandon mercy yet seek courage is fatal. With mercy, one wins in battle and
stands firm in defense; heaven saves and guards with mercy. -/
def chapter67 : Prop :=
  W.Possesses ⟦.sage⟧ ⟦.mercy⟧ ∧
  W.Possesses ⟦.sage⟧ ⟦.frugality⟧ ∧
  W.Possesses ⟦.sage⟧ ⟦.humility⟧ ∧
  ¬ W.Precedes ⟦.sage⟧ ⟦.world⟧ ∧
  (W.Dwells ⟦.sage⟧ ⟦.mercy⟧ → W.Overcomes ⟦.sage⟧ ⟦.war⟧) ∧
  W.Saves ⟦.heaven⟧ ⟦.mercy⟧

/-- **Chapter 68.** The good soldier is not warlike, the good fighter not
wrathful, the good victor does not contend, the good user of men puts himself
below them. This is the Virtue of non-contention, the power of using men, the
ultimate accord with heaven. -/
def chapter68 : Prop :=
  ¬ W.Is ⟦.master⟧ ⟦.war⟧ ∧
  ¬ W.Contends ⟦.master⟧ ∧
  W.Dwells ⟦.master⟧ ⟦.humility⟧ ∧
  W.Is ⟦.humility⟧ ⟦.virtue⟧ ∧
  W.Follows ⟦.master⟧ ⟦.heaven⟧

/-- **Chapter 69.** There is a saying among soldiers: I dare not be the host but
be the guest; dare not advance an inch but retreat a foot. This is marching
without marching, fighting without arms. No calamity is greater than
underestimating the enemy; to underestimate the enemy is to lose one's treasures.
When armies clash, the grieving side wins. -/
def chapter69 : Prop :=
  ¬ W.Precedes ⟦.master⟧ ⟦.war⟧ ∧
  W.Is ⟦.master⟧ ⟦.guest⟧ ∧
  (W.Reduces ⟦.master⟧ ⟦.war⟧ → ¬ W.Possesses ⟦.master⟧ ⟦.treasure⟧) ∧
  W.Overcomes ⟦.mourning⟧ ⟦.war⟧

/-- **Chapter 70.** My words are easy to understand and easy to practice, yet
none in the world can understand or practice them. Words have an ancestor, deeds
a master; because this is not known, I am not known. Those who know me are few,
and so I am honored. The sage wears coarse cloth but carries jade within. -/
def chapter70 : Prop :=
  W.Knows ⟦.sage⟧ ⟦.dao⟧ ∧
  ¬ W.Knows ⟦.world⟧ ⟦.dao⟧ ∧
  W.OriginOf ⟦.dao⟧ ⟦.name⟧ ∧
  W.Possesses ⟦.sage⟧ ⟦.jade⟧ ∧
  W.Is ⟦.sage⟧ ⟦.humility⟧

/-- **Chapter 71.** To know that you do not know is best; to not know yet think
you know is a flaw. Only by recognizing this flaw as a flaw can one be free of
it. The sage is free of the flaw because he treats the flaw as a flaw, and so is
free of it. -/
def chapter71 : Prop :=
  (¬ W.Knows ⟦.sage⟧ ⟦.knowledge⟧ → W.Is ⟦.sage⟧ ⟦.enlightenment⟧) ∧
  (W.Knows ⟦.sage⟧ ⟦.fault⟧ → ¬ W.Possesses ⟦.sage⟧ ⟦.fault⟧) ∧
  ¬ W.Possesses ⟦.sage⟧ ⟦.fault⟧

/-- **Chapter 72.** When the people do not fear authority, then great authority
has arrived. Do not crowd their dwellings, do not oppress their livelihood; only
by not oppressing are you not rejected. Hence the sage knows himself but does not
display himself, loves himself but is not self-important. He discards the one and
takes the other. -/
def chapter72 : Prop :=
  (¬ W.Possesses ⟦.people⟧ ⟦.fear⟧ → W.Exists_ ⟦.dignity⟧) ∧
  (¬ W.Harms ⟦.ruler⟧ ⟦.people⟧ → W.Trusts ⟦.people⟧ ⟦.ruler⟧) ∧
  W.Knows ⟦.sage⟧ ⟦.sage⟧ ∧
  W.Loves ⟦.sage⟧ ⟦.sage⟧ ∧
  ¬ W.Dwells ⟦.sage⟧ ⟦.pride⟧

/-- **Chapter 73.** Courage in daring kills; courage in not daring saves. These
two are sometimes beneficial, sometimes harmful; who knows what heaven hates?
The Dao of heaven does not contend yet wins, does not speak yet answers, is not
summoned yet comes, is at ease yet plans well. Heaven's net is vast; though its
mesh is wide, nothing slips through. -/
def chapter73 : Prop :=
  ¬ W.Contends ⟦.heaven⟧ ∧
  W.Overcomes ⟦.heaven⟧ ⟦.world⟧ ∧
  ¬ W.Speakable ⟦.heaven⟧ ∧
  (¬ W.Acts ⟦.heaven⟧ → W.Exists_ ⟦.heaven⟧) ∧
  (∀ x, ¬ ¬ W.Possesses ⟦.net⟧ x)

/-- **Chapter 74.** If people do not fear death, why threaten them with death?
If people always feared death, then whoever did wrong could be seized and killed
— but who would dare? There is always the executioner; to kill in his place is
like hewing wood in the master carpenter's place — one seldom escapes hurting
one's own hands. -/
def chapter74 : Prop :=
  ¬ W.Possesses ⟦.people⟧ ⟦.fear⟧ ∧
  W.Is ⟦.executioner⟧ ⟦.death⟧ ∧
  (W.Regards ⟦.ruler⟧ ⟦.executioner⟧ ⟦.carpenter⟧ → W.Harms ⟦.ruler⟧ ⟦.ruler⟧)

/-- **Chapter 75.** The people starve because their rulers eat too much in taxes;
the people are hard to govern because their rulers are too active; the people
take death lightly because they strive too hard for life. Only one who does not
strive for life is wiser than one who prizes it. -/
def chapter75 : Prop :=
  (W.Possesses ⟦.ruler⟧ ⟦.tax⟧ → ¬ W.Possesses ⟦.people⟧ ⟦.wealth⟧) ∧
  (W.Acts ⟦.ruler⟧ → W.Fails ⟦.ruler⟧) ∧
  (W.Loves ⟦.people⟧ ⟦.life⟧ → W.Is ⟦.people⟧ ⟦.death⟧) ∧
  (¬ W.Possesses ⟦.sage⟧ ⟦.desire⟧ → W.BetterThan ⟦.sage⟧ ⟦.people⟧)

/-- **Chapter 76.** At birth a person is soft and weak; at death stiff and hard.
Plants are tender and supple in life, dry and brittle in death. Thus the stiff
and hard are companions of death, the soft and weak companions of life. A rigid
army does not win, a rigid tree breaks. The strong and great take the lower
place, the soft and weak the higher. -/
def chapter76 : Prop :=
  (W.Is ⟦.life⟧ ⟦.soft⟧) ∧
  (W.Is ⟦.death⟧ ⟦.hard⟧) ∧
  W.Is ⟦.hard⟧ ⟦.death⟧ ∧
  W.Is ⟦.soft⟧ ⟦.life⟧ ∧
  (W.Is ⟦.war⟧ ⟦.strong⟧ → ¬ W.Overcomes ⟦.war⟧ ⟦.war⟧) ∧
  W.Dwells ⟦.strong⟧ ⟦.low⟧ ∧ W.Dwells ⟦.soft⟧ ⟦.high⟧

/-- **Chapter 77.** The Dao of heaven is like drawing a bow: the high is pressed
down, the low raised up; the excessive is reduced, the deficient supplemented.
Heaven's Dao reduces excess to supplement want; man's way does the opposite,
robbing the poor to serve the rich. Who can offer his surplus to the world? Only
one with the Dao. So the sage acts without presuming and takes no credit. -/
def chapter77 : Prop :=
  W.IsLike ⟦.heaven⟧ ⟦.bow⟧ ∧
  W.Reduces ⟦.heaven⟧ ⟦.fullness⟧ ∧
  W.Supplements ⟦.heaven⟧ ⟦.deficient⟧ ∧
  W.Reduces ⟦.people⟧ ⟦.deficient⟧ ∧
  W.Benefits ⟦.dao⟧ ⟦.world⟧ ∧
  W.Acts ⟦.sage⟧ ∧ ¬ W.Possesses ⟦.sage⟧ ⟦.pride⟧

/-- **Chapter 78.** Nothing in the world is softer than water, yet nothing
surpasses it in attacking the hard and strong; nothing can replace it. The weak
overcomes the strong, the soft the hard — all know it, none can practice it.
Hence the sage says: who bears the state's disgrace is its lord, who bears its
misfortunes is king of the world. True words seem paradoxical. -/
def chapter78 : Prop :=
  W.Is ⟦.water⟧ ⟦.soft⟧ ∧
  W.Overcomes ⟦.water⟧ ⟦.hard⟧ ∧
  W.Overcomes ⟦.weak⟧ ⟦.strong⟧ ∧
  W.Overcomes ⟦.soft⟧ ⟦.hard⟧ ∧
  W.Knows ⟦.world⟧ ⟦.dao⟧ ∧ ¬ W.Practices ⟦.world⟧ ⟦.dao⟧ ∧
  (W.Dwells ⟦.sage⟧ ⟦.disgrace⟧ → W.Is ⟦.sage⟧ ⟦.king⟧)

/-- **Chapter 79.** When a great grievance is settled, some grievance remains;
how can this be made good? The sage holds the left half of the tally but makes no
claim on others. The virtuous attend to the tally; the unvirtuous attend to
collection. The Dao of heaven has no favorites; it always sides with the good. -/
def chapter79 : Prop :=
  (W.Resolves ⟦.sage⟧ ⟦.blame⟧ → W.Exists_ ⟦.blame⟧) ∧
  ¬ W.Harms ⟦.sage⟧ ⟦.people⟧ ∧
  (W.Possesses ⟦.people⟧ ⟦.virtue⟧ → W.Resolves ⟦.people⟧ ⟦.blame⟧) ∧
  W.Loves ⟦.dao⟧ ⟦.good⟧

/-- **Chapter 80.** Let the state be small and the people few. Though there be
labor-saving tools, let them go unused; let the people value death and not
migrate far. Though there be boats and carts, let none ride them; though armor
and weapons, let none array them. Let people return to knotted cords, enjoy their
food, fine clothes, secure homes, and pleasant customs. Though neighboring states
are within sight and their dogs and roosters heard, the people grow old and die
without dealings with one another. -/
def chapter80 : Prop :=
  W.Is ⟦.nation⟧ ⟦.small⟧ ∧
  W.Dwells ⟦.people⟧ ⟦.death⟧ ∧
  W.Dwells ⟦.people⟧ ⟦.rope⟧ ∧
  W.Dwells ⟦.people⟧ ⟦.peace⟧ ∧
  (W.Dwells ⟦.people⟧ ⟦.contentment⟧ → ¬ W.Possesses ⟦.people⟧ ⟦.desire⟧)

/-- **Chapter 81.** Truthful words are not pleasant, pleasant words not truthful;
the good do not dispute, the disputatious are not good; the wise are not learned,
the learned are not wise. The sage does not hoard: the more he does for others,
the more he has; the more he gives, the more he gains. The Dao of heaven benefits
and does not harm; the Dao of the sage acts and does not contend. -/
def chapter81 : Prop :=
  (W.Is ⟦.faith⟧ ⟦.surface⟧ → False) ∧  -- truthful words are not "pretty" (mere surface)
  (W.Is ⟦.good⟧ ⟦.contention⟧ → False) ∧
  ¬ W.Possesses ⟦.sage⟧ ⟦.hoard⟧ ∧
  W.Benefits ⟦.heaven⟧ ⟦.world⟧ ∧ ¬ W.Harms ⟦.heaven⟧ ⟦.world⟧ ∧
  W.Acts ⟦.sage⟧ ∧ ¬ W.Contends ⟦.sage⟧

/-- A `Cosmos` *satisfies the Tao Te Ching* when all eighty-one chapters hold of
it.  This bundles the whole text as a single proposition about an abstract
world. -/
def SatisfiesTaoTeChing : Prop :=
  chapter1 W ∧ chapter2 W ∧ chapter3 W ∧ chapter4 W ∧ chapter5 W ∧
  chapter6 W ∧ chapter7 W ∧ chapter8 W ∧ chapter9 W ∧ chapter10 W ∧
  chapter11 W ∧ chapter12 W ∧ chapter13 W ∧ chapter14 W ∧ chapter15 W ∧
  chapter16 W ∧ chapter17 W ∧ chapter18 W ∧ chapter19 W ∧ chapter20 W ∧
  chapter21 W ∧ chapter22 W ∧ chapter23 W ∧ chapter24 W ∧ chapter25 W ∧
  chapter26 W ∧ chapter27 W ∧ chapter28 W ∧ chapter29 W ∧ chapter30 W ∧
  chapter31 W ∧ chapter32 W ∧ chapter33 W ∧ chapter34 W ∧ chapter35 W ∧
  chapter36 W ∧ chapter37 W ∧ chapter38 W ∧ chapter39 W ∧ chapter40 W ∧
  chapter41 W ∧ chapter42 W ∧ chapter43 W ∧ chapter44 W ∧ chapter45 W ∧
  chapter46 W ∧ chapter47 W ∧ chapter48 W ∧ chapter49 W ∧ chapter50 W ∧
  chapter51 W ∧ chapter52 W ∧ chapter53 W ∧ chapter54 W ∧ chapter55 W ∧
  chapter56 W ∧ chapter57 W ∧ chapter58 W ∧ chapter59 W ∧ chapter60 W ∧
  chapter61 W ∧ chapter62 W ∧ chapter63 W ∧ chapter64 W ∧ chapter65 W ∧
  chapter66 W ∧ chapter67 W ∧ chapter68 W ∧ chapter69 W ∧ chapter70 W ∧
  chapter71 W ∧ chapter72 W ∧ chapter73 W ∧ chapter74 W ∧ chapter75 W ∧
  chapter76 W ∧ chapter77 W ∧ chapter78 W ∧ chapter79 W ∧ chapter80 W ∧
  chapter81 W

end Cosmos
end TaoTeChing
