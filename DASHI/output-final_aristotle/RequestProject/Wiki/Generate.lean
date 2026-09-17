/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Wiki.Clean

/-!
# Generating pages

A page **generator** is a function from data to `Wikidata.Wiki.Page`.  The point of
`RequestProject.Wiki.Clean` is that a generator can be proved safe once and for
all: if everything it produces is hygienic, then the wikitext it prints reads back
as exactly the page it built (`Wikidata.Wiki.parsePage_render`), so no data can
smuggle markup into the result.

This file does that for the index generator used by
`RequestProject.Wiki.Pages`: a list of items, one line each, written as a call to
`{{Q}}` followed by the label.
-/

namespace Wikidata
namespace Wiki

/-! ## Reductions of the hygiene check -/

theorem pageCleanB_tmpl_cons (nm : String) (args : List Arg) (ns : Page) :
    pageCleanB (.tmpl nm args :: ns) = (nodeCleanB (.tmpl nm args) && pageCleanB ns) := rfl

theorem pageCleanB_param_cons (k : String) (d : Option String) (ns : Page) :
    pageCleanB (.param k d :: ns) = (nodeCleanB (.param k d) && pageCleanB ns) := rfl

theorem pageCleanB_text_nil (s : String) : pageCleanB [.text s] = nodeCleanB (.text s) := by
  simp [pageCleanB]

/-- A text run may head a hygienic page as long as the page does not itself begin
with a text run. -/
theorem pageCleanB_text_cons_of_head {s : String} {ns : Page} (hs : nodeCleanB (.text s) = true)
    (hns : pageCleanB ns = true) (hhead : ∀ t, ns.head? ≠ some (.text t)) :
    pageCleanB (.text s :: ns) = true := by
  cases ns with
  | nil => rw [pageCleanB_text_nil]; exact hs
  | cons m ms =>
      cases m with
      | text t => exact absurd rfl (hhead t)
      | tmpl nm args =>
          show (nodeCleanB (.text s) && pageCleanB (.tmpl nm args :: ms)) = true
          rw [hs, hns, Bool.and_self]
      | param k d =>
          show (nodeCleanB (.text s) && pageCleanB (.param k d :: ms)) = true
          rw [hs, hns, Bool.and_self]

/-! ## The index generator -/

/-- An item to be listed: its identifier and its label. -/
abbrev IndexItem := String × String

/-- When an item is safe to list: the identifier is a hygienic argument, and the
line it produces is a hygienic text run. -/
def indexOk (e : IndexItem) : Bool :=
  argCleanB ⟨none, e.1⟩ && textCleanB (" — " ++ e.2 ++ "\n")

/-- **The index generator.**  One line per item: a call to the template `nm` on
the identifier, then the label.  With `nm = "Q"` a line reads `{{Q|id}} — label`. -/
def indexPage (nm : String) : List IndexItem → Page
  | [] => []
  | e :: es => .tmpl nm [⟨none, e.1⟩] :: .text (" — " ++ e.2 ++ "\n") :: indexPage nm es

/-- A generated index with a heading paragraph in front of it. -/
def sectionPage (nm heading : String) (items : List IndexItem) : Page :=
  .text heading :: indexPage nm items

theorem nodeCleanB_call {nm v : String} (hn : nameCleanB nm = true)
    (h : argCleanB ⟨none, v⟩ = true) : nodeCleanB (.tmpl nm [⟨none, v⟩]) = true := by
  simp [nodeCleanB, hn, h]

theorem indexPage_head_ne_text (nm : String) (items : List IndexItem) (s : String) :
    (indexPage nm items).head? ≠ some (.text s) := by
  cases items <;> simp [indexPage]

/-- **The generated index is hygienic.** -/
theorem indexPage_clean (nm : String) (hn : nameCleanB nm = true) :
    ∀ items : List IndexItem, items.all indexOk = true →
    pageCleanB (indexPage nm items) = true := by
  intro items
  induction items with
  | nil => intro _; rfl
  | cons e es ih =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true, indexOk] at h
      obtain ⟨⟨hq, ht⟩, hes⟩ := h
      have h2 : nodeCleanB (.text (" — " ++ e.2 ++ "\n")) = true := ht
      rw [indexPage, pageCleanB_tmpl_cons, nodeCleanB_call hn hq, Bool.true_and]
      exact pageCleanB_text_cons_of_head h2 (ih hes) (indexPage_head_ne_text nm es)

/-- **A generated index prints to wikitext that reads back as itself.** -/
theorem indexPage_roundTrip (nm : String) (hn : nameCleanB nm = true) (items : List IndexItem)
    (h : items.all indexOk = true) :
    parsePage (render (indexPage nm items)) = some (indexPage nm items) :=
  parsePage_render (indexPage_clean nm hn items h)

/-- **A generated section is hygienic.** -/
theorem sectionPage_clean (nm heading : String) (hn : nameCleanB nm = true)
    (items : List IndexItem) (hh : textCleanB heading = true) (h : items.all indexOk = true) :
    pageCleanB (sectionPage nm heading items) = true :=
  pageCleanB_text_cons_of_head hh (indexPage_clean nm hn items h) (indexPage_head_ne_text nm items)

/-- **A generated section prints to wikitext that reads back as itself.** -/
theorem sectionPage_roundTrip (nm heading : String) (hn : nameCleanB nm = true)
    (items : List IndexItem) (hh : textCleanB heading = true) (h : items.all indexOk = true) :
    parsePage (render (sectionPage nm heading items)) = some (sectionPage nm heading items) :=
  parsePage_render (sectionPage_clean nm heading hn items hh h)

end Wiki
end Wikidata
