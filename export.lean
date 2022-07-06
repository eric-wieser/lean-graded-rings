/- This file exports file and line information for use in LaTeX references. -/

import all

import tactic.core

open tactic

meta structure decl_info :=
(name : name)
(filename : string)
(line : ℕ)

meta def process_decl (d : declaration) : tactic (option decl_info) :=
do 
  ff ← d.in_current_file | return none,
  e ← get_env,
  let decl_name := d.to_name,
  ff ← pure (decl_name.is_internal ∨ d.is_auto_generated e : bool) | return none,
  some filename ← return (e.decl_olean decl_name) | return none,
  let parts := filename.split (= '/'),
  some ⟨line, _⟩ ← return (e.decl_pos decl_name) | return none,
  return $ some ⟨decl_name, filename, line⟩

def path_split (path : string) : option string × string :=
match (path.split (= '/')).reverse with
| [] := (none, "/")
| [a] := (none, a)
| (a :: as) := ("/".intercalate as.reverse, a)
end

/-- Split a lean path into a project/parent pair -/
def project_file_split (path : string) : io (option string × string) :=
do
  (parent, some rest, tt) ← (io.iterate (some path, (none : option string), ff) $ λ state, do {
    (some p, old_rest, ff) ← pure state | pure none,
    (parent, rest) ← pure (path_split p),
    let rest := (match old_rest with
    | some r := rest ++ "/" ++ r
    | none := rest
    end),
    some parent ← pure parent | pure (some (parent, old_rest, tt)),
    found ← io.fs.file_exists (parent ++ "/leanpkg.toml"),
    pure (some (parent, some rest, found)) }),
  pure (parent, rest)

/-- A version of `list.map` for `io` that does not consume the whole stack -/
def list.mmap_io {α β : Type*} (f : α → io β) (l : list α) : io (list β) :=
do
  (_, bs) ← io.iterate (l, ([] : list β)) (λ state, do {
    (a :: as, bs) ← pure state | return none,
    b ← f a,
    return (some (as, b :: bs))
  }),
  pure bs

meta def main : io unit :=
do
  infos ← io.run_tactic $ do
  { e ← get_env,
    e.get_decls.mmap process_decl },
  io.put_str_ln "\\makeatletter",
  io.put_str_ln "\\@namedef{lean-ref-github}{https://github.com/eric-wieser/lean-graded-rings}",
  sha ← io.cmd { cmd := "git", args := ["rev-parse", "HEAD"] },
  let sha := sha.pop_back,  -- remove trailing newline
  io.put_str_ln (format!"\\@namedef{{lean-ref-sha}}{{{sha}}}").to_string,
  infos.mmap_io $ λ di : option decl_info, do
  { some di ← pure di | pure (),
    (some p, file) ← project_file_split di.filename | pure (),
    tt ← pure ("lean-graded-rings".is_suffix_of p) | pure (),
    io.put_str_ln (format!"\\@namedef{{lean-ref-file@{di.name}}}{{{file}}}" ++
                   format!"\\@namedef{{lean-ref-line@{di.name}}}{{{di.line}}}").to_string },
  io.put_str_ln "\\makeatother"