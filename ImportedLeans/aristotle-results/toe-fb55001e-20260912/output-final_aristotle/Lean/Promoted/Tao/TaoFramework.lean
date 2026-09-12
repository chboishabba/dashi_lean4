import Mathlib

/-!
# A formalization of the *Tao Te Ching* (道德經)

This file sets up an abstract logical framework in which the assertions of the
*Tao Te Ching* (attributed to Laozi) can be stated.  The text is poetic and
philosophical, so a literal mathematical formalization is impossible; instead we
take the following stance.

* The **domain of discourse** is an abstract type `E` of "entities / concepts".
* Every concrete *term* that appears in the text and that we cannot define
  (the Dao, Virtue, Heaven, the Sage, beauty, water, …) is named by an element
  of an enumeration `Concept`, interpreted into `E` by a denotation function
  `den : Concept → E`.
* Every *relation or modality* used by the text ("is eternal", "gives birth to",
  "overcomes", "is like", …) is a primitive predicate.

All of these undefined primitives are collected as the fields of a single
structure `Cosmos`.  A particular interpretation of the world is a term of type
`Cosmos`; each chapter of the text is then a `Prop`-valued statement about a
`Cosmos`.

> **Note on axioms.**  The instruction was to introduce "a new axiom for each
> term that cannot be defined".  Rather than using Lean `axiom` declarations
> (which would assert facts globally and are unsound to add freely), we realise
> each undefined term and relation *soundly* as a field of the parameter
> structure `Cosmos`.  This has exactly the intended meaning — the terms are
> genuine primitives — without asserting anything unproven.

The chapters themselves are recorded in `TaoShang.lean` (上篇, chapters 1–37) and
`TaoXia.lean` (下篇, chapters 38–81).
-/

namespace TaoTeChing

/-- The primitive *terms* (concepts) named in the text.  None of these can be
defined; each is interpreted abstractly via `Cosmos.den`. -/
inductive Concept where
  -- Core ontology
  | dao | virtue | nature | heaven | earth | world | myriad | thing
  | name | form | image | essence | breath | yin | yang | harmony
  | unity | two | three | root | origin | «return» | destiny
  | mystery | wonder | gate | mother | child | infant | spirit | valley
  | light | dust | sharpness | complexity | depth | surface | boundary
  -- People and agents
  | sage | people | ruler | king | leader | gentleman | master | scholar
  | worthy | teacher | resource | host | guest | executioner | carpenter
  | descendants | neighbor
  -- Qualities and opposites
  | beauty | ugliness | good | evil | being | nonBeing
  | difficult | easy | long | short | high | low | sound | voice | front | back
  | soft | hard | weak | strong | female | male
  | fullness | emptiness | life | death | heavy | lightWeight
  | stillness | motion | restless | white | black | glory | disgrace
  | fortune | adversity | great | small | straight | crooked | whole | deficient
  | completion | freshness | clarity | eternal | enlightenment | profound
  | invisible | soundless | intangible | limitless
  -- Action and mind
  | nonAction | action | contention | desire | knowledge | wisdom | cleverness
  | learning | simplicity | purity | mind | belly | will | bones
  | anxiety | fear | trust | faith | love | credit | achievement
  | restraint | contentment | pride | fool
  -- Society and politics
  | benevolence | righteousness | ritual | propriety | filialPiety | affection
  | loyalty | hypocrisy | holiness | war | weapon | peace | wealth | goods
  | fame | treasure | mercy | frugality | humility | reward | punishment
  | law | thief | taboo | sin | fault | guilt | blame | dignity
  | governance | nation | court | field | storehouse | tax
  -- Objects and images
  | water | strawDog | bellows | spoke | hub | vessel | room | door | window
  | clay | color | music | flavor | bow | fish | gem | stone | jade
  | horse | chariot | dew | river | ocean | stream | path | tree | sprout
  | tower | mound | journey | step | ice | wood | sword | tiger | beast | bird
  | net | dawn | winter | rope
  -- Further notions used in paradoxes / political maxims
  | principle | hoard | cost | victory | mourning | transformation
  | example | foreknowledge | inauspicious | cold | heat
  deriving DecidableEq, Repr

/-- An abstract interpretation of the world: it fixes the domain `E`, the
denotation of every primitive *term*, and the meaning of every primitive
*relation/modality* used by the text. -/
structure Cosmos where
  /-- The domain of entities / concepts. -/
  E : Type
  /-- Denotation of the primitive terms. -/
  den : Concept → E
  -- Unary modalities / predicates
  /-- `x` is eternal / constant (恆 / 常). -/
  Eternal   : E → Prop
  /-- `x` can be spoken of / stated (可道). -/
  Speakable : E → Prop
  /-- `x` can be named (可名). -/
  Nameable  : E → Prop
  /-- `x` is empty (虛 / 沖). -/
  Empty     : E → Prop
  /-- `x` endures / is long-lived (久 / 長久). -/
  Endures   : E → Prop
  /-- `x` contends / quarrels (爭). -/
  Contends  : E → Prop
  /-- `x` engages in (deliberate) action (為 / 有為). -/
  Acts      : E → Prop
  /-- `x` exists / is present (存 / 有). -/
  Exists_   : E → Prop
  /-- `x` fails / comes to an early end (敗 / 早已). -/
  Fails     : E → Prop
  /-- `x` survives / preserves itself (身存). -/
  Survives  : E → Prop
  -- Binary relations
  /-- `x` is (a) `y`; general predication (是 / 為). -/
  Is        : E → E → Prop
  /-- `x` is not (the) `y` (非). -/
  IsNot     : E → E → Prop
  /-- `x` is like / seems like `y` (若 / 似 / 猶 / 比). -/
  IsLike    : E → E → Prop
  /-- `x` is the origin / source / root of `y` (始 / 宗 / 根). -/
  OriginOf  : E → E → Prop
  /-- `x` is the mother of `y` (母). -/
  MotherOf  : E → E → Prop
  /-- `x` gives birth to `y` (生). -/
  GivesBirthTo : E → E → Prop
  /-- `x` and `y` complete / shape one another (相生 / 相成 / 相形 / 相傾 / 相和 / 相隨). -/
  Complements  : E → E → Prop
  /-- `x` overcomes / is victorious over `y` (勝). -/
  Overcomes : E → E → Prop
  /-- `x` is better than `y`. -/
  BetterThan : E → E → Prop
  /-- `x` follows / takes its law from `y` (法 / 從 / 隨). -/
  Follows   : E → E → Prop
  /-- `x` knows `y` (知). -/
  Knows     : E → E → Prop
  /-- `x` benefits `y` (利). -/
  Benefits  : E → E → Prop
  /-- `x` harms `y` (害). -/
  Harms     : E → E → Prop
  /-- `x` possesses / owns `y` (有). -/
  Possesses : E → E → Prop
  /-- `x` dwells in / abides in / stays with `y` (處 / 居 / 守). -/
  Dwells    : E → E → Prop
  /-- `x` practices / carries out `y` (行 / 為). -/
  Practices : E → E → Prop
  /-- `x` returns to `y` (復歸 / 歸). -/
  Returns   : E → E → Prop
  /-- `x` precedes / is ahead of `y` (先). -/
  Precedes  : E → E → Prop
  /-- `x` nourishes / rears `y` (畜 / 養). -/
  Nourishes : E → E → Prop
  /-- `x` loves `y` (愛). -/
  Loves     : E → E → Prop
  /-- `x` trusts `y` (信). -/
  Trusts    : E → E → Prop
  /-- `x` reduces / diminishes `y` (損). -/
  Reduces   : E → E → Prop
  /-- `x` supplements / augments `y` (補 / 益). -/
  Supplements : E → E → Prop
  /-- `x` saves / rescues `y` (救). -/
  Saves     : E → E → Prop
  /-- `x` abandons / discards `y` (棄 / 去). -/
  Abandons  : E → E → Prop
  /-- `x` takes / conquers `y` (取). -/
  Conquers  : E → E → Prop
  /-- `x` transforms / becomes `y` (化). -/
  Transforms : E → E → Prop
  /-- `x` produces `y` (生 in the sense of "produces but does not own"). -/
  Produces  : E → E → Prop
  /-- `x` resolves / harmonizes `y` (和 / 解). -/
  Resolves  : E → E → Prop
  -- Ternary relation
  /-- `s` regards / treats `o` as `p` (以 o 為 p). -/
  Regards   : E → E → E → Prop

end TaoTeChing
