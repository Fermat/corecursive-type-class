module q where
axiom (Q (F (G x)), Q x) => Q (F x)
axiom Q Z
axiom  Q x => Q (G x)
lemma Q x => Q (F x)
