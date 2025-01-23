#let conf(
  title: none,
  authors: (),
  abstract: [],
  doc,
) = {
  set align(center)
  text(size: 17pt, title)
  set text(font: "New Computer Modern", size: 11pt)

  let count = authors.len()
  let ncols = calc.min(count, 3)
  grid(
    columns: (1fr,) * ncols,
    row-gutter: 24pt,
    ..authors.map(author => [
      #author.name \
      #author.affiliation \
      #link("mailto:" + author.email)
    ]),
  )

  par(justify: false)[
    *Abstract* \
    #abstract
  ]
  set par(justify: true)
  set page(numbering: "1")

  set align(left)
  set cite(form: "prose")  

  doc
}
