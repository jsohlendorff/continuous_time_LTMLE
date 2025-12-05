#import "@preview/ctheorems:1.1.3": *
#import "shortcuts.typ": *
#import "graph.typ": *

//#show: checklist
#let citep(label) = cite(label, form: "normal")

//#let comment = comment.with(inline:true)

#show: thmrules.with(qed-symbol: $square$)

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"), base_level: 0)
#let corollary = thmbox("corollary", "Corollary", fill: rgb("#eeffee"), base_level: 0)
#let algorithm = thmbox("algorithm", "Algorithm", fill: rgb("#f5b8c3"), base_level: 0)
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee"), base_level: 0)
#let assumption = thmbox("assumption", "Assumption", fill: rgb("#eeeeff"), base_level: 0)
#let definition = thmbox("definition", "Definition", fill: rgb("#ffeeee"), base_level: 0)
#let proof = thmproof("proof", "Proof")
