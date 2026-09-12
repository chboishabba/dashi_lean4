def s : String := "#eval IO.println s!\"def s : String := {repr s}\\n{s}\""
#eval IO.println s!"def s : String := {repr s}\n{s}"
