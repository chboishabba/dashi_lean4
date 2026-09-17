/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Cli.Format

/-!
# Machine-readable report files: CSV, HTML and SVG

The diagnostic layers of the library (`RequestProject.Diagnostics`,
`RequestProject.SeriesDiagnostics`, `RequestProject.TaxaDiagnostics`,
`RequestProject.KinshipDiagnostics`, `RequestProject.ParentingDiagnostics`) all
produce *witnessed* issues: each problem names the items it is about.  This file
is the output side of that: three renderers that turn a table of rows into files
other tools can read.

* **CSV** — `Wikidata.Report.csvText`.  Every field is quoted and every quote is
  doubled, so a field may contain commas and quotation marks.  The round trip is
  proved: `Wikidata.Report.parseCsvRow_csvRow` says reading a rendered row back
  returns exactly the fields that were written, and
  `Wikidata.Report.parseCsvText_csvText` says the same of a whole file, so a
  spreadsheet import cannot silently mangle a report.
* **HTML** — `Wikidata.Report.htmlText`, a self-contained page.  All data is
  escaped, and `Wikidata.Report.htmlEscape_no_markup` proves that the escaped
  form of a field contains no `<`, `>` or `"`, so no identifier can inject
  markup.  `Wikidata.Report.htmlRowLines_length` says the page has exactly one
  row per issue.
* **SVG** — `Wikidata.Report.svgText`, a bar chart of the counts.
  `Wikidata.Report.svgBarLines_length` says it draws exactly one bar per entry.

Nothing here knows what an issue is; `RequestProject.Reports` builds the rows.
-/

namespace Wikidata
namespace Report

open Cli (joinChar)

/-! ## CSV -/

/-- Doubles every quotation mark, the CSV escape convention. -/
def escChars : List Char → List Char
  | [] => []
  | '"' :: cs => '"' :: '"' :: escChars cs
  | c :: cs => c :: escChars cs

/-- One CSV field: always quoted, with inner quotes doubled. -/
def quotedChars (s : String) : List Char := '"' :: (escChars s.toList ++ ['"'])

/-- One CSV record, as characters. -/
def csvRowChars : List String → List Char
  | [] => []
  | [f] => quotedChars f
  | f :: fs => quotedChars f ++ ',' :: csvRowChars fs

/-- One CSV record. -/
def csvRow (fs : List String) : String := String.ofList (csvRowChars fs)

/-- The lines of a CSV file: the header, then one line per row. -/
def csvLines (header : List String) (rows : List (List String)) : List String :=
  csvRow header :: rows.map csvRow

/-- A CSV file: a header line and one line per row. -/
def csvText (header : List String) (rows : List (List String)) : String :=
  joinChar '\n' (csvLines header rows)

/-! ### Reading CSV back -/

/-- Reads the body of a quoted field, after the opening quote: returns the
unescaped content and what follows the closing quote. -/
def fieldBody : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: '"' :: cs => (fieldBody cs).map fun p => ('"' :: p.1, p.2)
  | '"' :: cs => some ([], cs)
  | c :: cs => (fieldBody cs).map fun p => (c :: p.1, p.2)

theorem fieldBody_length : ∀ {cs b r : List Char},
    fieldBody cs = some (b, r) → r.length < cs.length := by
  intro cs
  induction cs using fieldBody.induct with
  | case1 => intro b r h; simp [fieldBody] at h
  | case2 cs ih =>
      intro b r h
      simp only [fieldBody, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, hbr⟩ := h
      have := ih (b := p.1) (r := p.2) hp
      cases hbr
      simp only [List.length_cons]
      omega
  | case3 cs _ =>
      intro b r h
      simp only [fieldBody] at h
      cases h
      simp
  | case4 c cs _ _ ih =>
      intro b r h
      simp only [fieldBody, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, hbr⟩ := h
      have := ih (b := p.1) (r := p.2) hp
      cases hbr
      simp only [List.length_cons]
      omega

/-- Reads a CSV record: a non-empty comma separated list of quoted fields. -/
def parseCsvRowChars : List Char → Option (List String)
  | '"' :: cs =>
      match h : fieldBody cs with
      | some (b, []) => some [String.ofList b]
      | some (b, ',' :: r) =>
          have : r.length < cs.length + 1 := by
            have := fieldBody_length h
            simp only [List.length_cons] at this
            omega
          (parseCsvRowChars r).map (String.ofList b :: ·)
      | _ => none
  | _ => none
termination_by cs => cs.length

/-- Reads a CSV record. -/
def parseCsvRow (s : String) : Option (List String) := parseCsvRowChars s.toList

/-- Reads a CSV file: one record per line. -/
def parseCsvText (s : String) : Option (List (List String)) :=
  (Cli.splitChar '\n' s).mapM parseCsvRow

/-! ### The round trip -/

theorem fieldBody_esc (s : List Char) {rest : List Char} (h : ∀ r, rest ≠ '"' :: r) :
    fieldBody (escChars s ++ '"' :: rest) = some (s, rest) := by
  induction s with
  | nil =>
      cases rest with
      | nil => simp [escChars, fieldBody]
      | cons c cs =>
          -- the closing quote is not doubled: `h` says `rest` does not start with `"`
          simp only [escChars, List.nil_append, fieldBody]
  | cons c s ih =>
      by_cases hc : c = '"'
      · subst hc
        simp [escChars, fieldBody, ih]
      · simp [escChars, fieldBody, hc, ih]

theorem parseCsvRowChars_csvRowChars :
    ∀ {fs : List String}, fs ≠ [] → parseCsvRowChars (csvRowChars fs) = some fs := by
  intro fs
  induction fs with
  | nil => intro h; exact absurd rfl h
  | cons f fs ih =>
      intro _
      cases fs with
      | nil =>
          simp only [csvRowChars, quotedChars, parseCsvRowChars]
          rw [fieldBody_esc f.toList (by simp)]
          simp
      | cons g gs =>
          have hne : (g :: gs) ≠ ([] : List String) := by simp
          simp only [csvRowChars, quotedChars, List.cons_append, List.append_assoc,
            parseCsvRowChars]
          rw [fieldBody_esc f.toList (by simp)]
          simp [ih hne]

/-- **A rendered CSV record reads back exactly.** -/
theorem parseCsvRow_csvRow {fs : List String} (h : fs ≠ []) : parseCsvRow (csvRow fs) = some fs := by
  simpa [parseCsvRow, csvRow] using parseCsvRowChars_csvRowChars h

/-- A rendered record contains no newline, so records cannot run into each other. -/
theorem newline_notMem_escChars (s : List Char) (h : '\n' ∉ s) : '\n' ∉ escChars s := by
  induction s with
  | nil => simp [escChars]
  | cons c cs ih =>
      by_cases hc : c = '"'
      · subst hc
        simp only [escChars, List.mem_cons, not_or]
        refine ⟨by decide, by decide, ih (fun hm => h (List.mem_cons_of_mem _ hm))⟩
      · simp only [escChars, List.mem_cons, not_or]
        exact ⟨fun he => h (he ▸ List.mem_cons_self), ih fun hm => h (List.mem_cons_of_mem _ hm)⟩

theorem newline_notMem_quotedChars {f : String} (h : '\n' ∉ f.toList) :
    '\n' ∉ quotedChars f := by
  intro hm
  simp only [quotedChars, List.mem_cons, List.mem_append] at hm
  rcases hm with h1 | h1 | h1
  · exact absurd h1 (by decide)
  · exact newline_notMem_escChars _ h h1
  · exact absurd h1 (by decide)

theorem newline_notMem_csvRowChars :
    ∀ {fs : List String}, (∀ f ∈ fs, '\n' ∉ f.toList) → '\n' ∉ csvRowChars fs := by
  intro fs
  induction fs with
  | nil => intro _; simp [csvRowChars]
  | cons f fs ih =>
      intro h
      have hf : '\n' ∉ quotedChars f := newline_notMem_quotedChars (h f List.mem_cons_self)
      have hrest : '\n' ∉ csvRowChars fs := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
      cases fs with
      | nil => simpa [csvRowChars] using hf
      | cons g gs =>
          intro hm
          simp only [csvRowChars, List.mem_append, List.mem_cons] at hm
          rcases hm with h1 | h1 | h1
          · exact hf h1
          · exact absurd h1 (by decide)
          · exact hrest h1

theorem mapM_parseCsvRow : ∀ {rows : List (List String)}, (∀ r ∈ rows, r ≠ []) →
    (rows.map csvRow).mapM parseCsvRow = some rows := by
  intro rows
  induction rows with
  | nil => intro _; simp
  | cons r rs ih =>
      intro h
      rw [List.map_cons, List.mapM_cons, parseCsvRow_csvRow (h r List.mem_cons_self),
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
      rfl

/-- **A rendered CSV file reads back exactly**, provided no field contains a
newline (the report rows never do: their fields are identifiers and fixed
phrases). -/
theorem parseCsvText_csvText {header : List String} {rows : List (List String)}
    (hh : header ≠ []) (hhn : ∀ f ∈ header, '\n' ∉ f.toList)
    (hr : ∀ r ∈ rows, r ≠ [] ∧ ∀ f ∈ r, '\n' ∉ f.toList) :
    parseCsvText (csvText header rows) = some (header :: rows) := by
  have hclean : ∀ x ∈ csvLines header rows, '\n' ∉ x.toList := by
    intro x hx
    simp only [csvLines, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨r, hrmem, rfl⟩
    · simpa [csvRow] using newline_notMem_csvRowChars hhn
    · simpa [csvRow] using newline_notMem_csvRowChars (hr r hrmem).2
  have hsplit : Cli.splitChar '\n' (csvText header rows) = csvLines header rows :=
    Cli.splitChar_joinChar '\n' _ hclean (by simp [csvLines])
  rw [parseCsvText, hsplit, csvLines, List.mapM_cons, parseCsvRow_csvRow hh,
    mapM_parseCsvRow fun r hrmem => (hr r hrmem).1]
  rfl

/-! ## HTML -/

/-- Escapes the characters that carry meaning in HTML. -/
def htmlEsc : List Char → List Char
  | [] => []
  | '&' :: cs => '&' :: 'a' :: 'm' :: 'p' :: ';' :: htmlEsc cs
  | '<' :: cs => '&' :: 'l' :: 't' :: ';' :: htmlEsc cs
  | '>' :: cs => '&' :: 'g' :: 't' :: ';' :: htmlEsc cs
  | '"' :: cs => '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: htmlEsc cs
  | c :: cs => c :: htmlEsc cs

/-- Escapes a string for inclusion in an HTML page. -/
def htmlEscape (s : String) : String := String.ofList (htmlEsc s.toList)

theorem notMem_htmlEsc {d : Char} (hd : d = '<' ∨ d = '>' ∨ d = '"') :
    ∀ cs : List Char, d ∉ htmlEsc cs := by
  intro cs
  induction cs using htmlEsc.induct with
  | case1 => simp [htmlEsc]
  | case2 cs ih =>
      simp only [htmlEsc, List.mem_cons, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ih⟩ <;> rcases hd with rfl | rfl | rfl <;> decide
  | case3 cs ih =>
      simp only [htmlEsc, List.mem_cons, not_or]
      refine ⟨?_, ?_, ?_, ?_, ih⟩ <;> rcases hd with rfl | rfl | rfl <;> decide
  | case4 cs ih =>
      simp only [htmlEsc, List.mem_cons, not_or]
      refine ⟨?_, ?_, ?_, ?_, ih⟩ <;> rcases hd with rfl | rfl | rfl <;> decide
  | case5 cs ih =>
      simp only [htmlEsc, List.mem_cons, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ih⟩ <;> rcases hd with rfl | rfl | rfl <;> decide
  | case6 c cs h1 h2 h3 h4 ih =>
      simp only [htmlEsc, List.mem_cons, not_or]
      refine ⟨?_, ih⟩
      rcases hd with rfl | rfl | rfl
      · exact fun hc => h2 (by rw [hc])
      · exact fun hc => h3 (by rw [hc])
      · exact fun hc => h4 (by rw [hc])

/-- **Escaped data cannot inject markup**: no `<`, `>` or `"` survives. -/
theorem htmlEscape_no_markup (s : String) :
    '<' ∉ (htmlEscape s).toList ∧ '>' ∉ (htmlEscape s).toList ∧
      '"' ∉ (htmlEscape s).toList := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [htmlEscape, String.toList_ofList]
  · exact notMem_htmlEsc (Or.inl rfl) _
  · exact notMem_htmlEsc (Or.inr (Or.inl rfl)) _
  · exact notMem_htmlEsc (Or.inr (Or.inr rfl)) _

/-- One cell of the HTML table. -/
def htmlCell (s : String) : String := "<td>" ++ htmlEscape s ++ "</td>"

/-- One row of the HTML table.  `cls` becomes the row's CSS class, so the page
can be filtered and coloured by severity. -/
def htmlRowLine (cls : String) (fs : List String) : String :=
  "<tr class=\"" ++ htmlEscape cls ++ "\">" ++
    String.join (fs.map htmlCell) ++ "</tr>"

/-- The body lines of the HTML table: one per row. -/
def htmlRowLines (rows : List (String × List String)) : List String :=
  rows.map fun r => htmlRowLine r.1 r.2

/-- **One HTML row per issue** — the page loses nothing. -/
theorem htmlRowLines_length (rows : List (String × List String)) :
    (htmlRowLines rows).length = rows.length := by
  simp [htmlRowLines]

/-- The header row of the HTML table. -/
def htmlHeadLine (header : List String) : String :=
  "<tr>" ++ String.join (header.map fun h => "<th>" ++ htmlEscape h ++ "</th>") ++ "</tr>"

/-- The stylesheet of the generated page. -/
def htmlStyle : String :=
  "body{font-family:-apple-system,Segoe UI,Helvetica,Arial,sans-serif;margin:2rem;color:#1b1b1f}\n" ++
  "h1{font-size:1.4rem} h2{font-size:1.05rem;margin-top:2rem}\n" ++
  "table{border-collapse:collapse;font-size:.85rem;width:100%}\n" ++
  "th,td{border:1px solid #d7d7de;padding:.25rem .5rem;text-align:left;vertical-align:top}\n" ++
  "th{background:#f2f2f5}\n" ++
  "tr.error td:nth-child(3){color:#a4262c;font-weight:600}\n" ++
  "tr.warning td:nth-child(3){color:#8a6d00;font-weight:600}\n" ++
  "tr.error:hover,tr.warning:hover{background:#f7f9ff}\n" ++
  "code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace}\n" ++
  ".meta{color:#5b5b66;font-size:.85rem}"

/-- A complete HTML page: a title, some prose, a summary table and the rows. -/
def htmlText (title : String) (intro : String) (header : List String)
    (summary : List (String × List String)) (summaryHeader : List String)
    (rows : List (String × List String)) : String :=
  Cli.joinChar '\n'
    (["<!DOCTYPE html>", "<html lang=\"en\">", "<head>", "<meta charset=\"utf-8\">",
      "<title>" ++ htmlEscape title ++ "</title>", "<style>", htmlStyle, "</style>",
      "</head>", "<body>",
      "<h1>" ++ htmlEscape title ++ "</h1>",
      "<p class=\"meta\">" ++ htmlEscape intro ++ "</p>",
      "<h2>By error type</h2>", "<table>", htmlHeadLine summaryHeader] ++
     htmlRowLines summary ++
     ["</table>", "<h2>Issues</h2>", "<table>", htmlHeadLine header] ++
     htmlRowLines rows ++
     ["</table>", "</body>", "</html>"])

/-! ## SVG -/

/-- A number, as decimal text. -/
def num (n : ℕ) : String := Cli.renderNat n

/-- One bar of the chart: a label, a count, and a colour. -/
structure Bar where
  /-- What is counted: the error type. -/
  label : String
  /-- How many issues of this type there are. -/
  count : ℕ
  /-- The status colour: red for errors, amber for warnings. -/
  colour : String
deriving Repr, Inhabited, DecidableEq

/-- The width in pixels of a bar counting `n` issues, when the largest bar
counts `m`. -/
def barWidth (m n : ℕ) : ℕ := if m = 0 then 0 else (520 * n) / m

/-- The lines drawing one bar, at vertical offset `i`. -/
def svgBarLine (m : ℕ) (i : ℕ) (b : Bar) : String :=
  let y := 96 + 26 * i
  "<g class=\"bar\">" ++
    "<text x=\"250\" y=\"" ++ num (y + 13) ++ "\" text-anchor=\"end\" class=\"lbl\">" ++
      htmlEscape b.label ++ "</text>" ++
    "<rect x=\"262\" y=\"" ++ num (y + 3) ++ "\" width=\"" ++ num (barWidth m b.count) ++
      "\" height=\"16\" rx=\"3\" fill=\"" ++ htmlEscape b.colour ++ "\"/>" ++
    "<text x=\"" ++ num (270 + barWidth m b.count) ++ "\" y=\"" ++ num (y + 16) ++
      "\" class=\"cnt\">" ++ num b.count ++ "</text>" ++
  "</g>"

/-- The bar lines of the chart: one per entry. -/
def svgBarLines (bars : List Bar) : List String :=
  let m := bars.foldl (fun acc b => max acc b.count) 0
  bars.zipIdx.map fun p => svgBarLine m p.2 p.1

/-- **One bar per error type.** -/
theorem svgBarLines_length (bars : List Bar) : (svgBarLines bars).length = bars.length := by
  simp [svgBarLines]

/-- A complete SVG chart of the report. -/
def svgText (title : String) (subtitle : String) (bars : List Bar) : String :=
  let height := 130 + 26 * bars.length
  Cli.joinChar '\n'
    (["<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"860\" height=\"" ++ num height ++
        "\" viewBox=\"0 0 860 " ++ num height ++ "\" font-family=\"-apple-system,Segoe UI,Helvetica,Arial,sans-serif\">",
      "<rect width=\"860\" height=\"" ++ num height ++ "\" fill=\"#ffffff\"/>",
      "<style>.ttl{font-size:20px;font-weight:600;fill:#1b1b1f}" ++
        ".sub{font-size:12px;fill:#5b5b66}.lbl{font-size:12px;fill:#1b1b1f}" ++
        ".cnt{font-size:12px;fill:#5b5b66}</style>",
      "<text x=\"28\" y=\"44\" class=\"ttl\">" ++ htmlEscape title ++ "</text>",
      "<text x=\"28\" y=\"66\" class=\"sub\">" ++ htmlEscape subtitle ++ "</text>",
      "<line x1=\"261\" y1=\"92\" x2=\"261\" y2=\"" ++ num (96 + 26 * bars.length) ++
        "\" stroke=\"#d7d7de\"/>"] ++
     svgBarLines bars ++
     ["</svg>"])

end Report
end Wikidata
