// acronyms 

#let prefix = "acronym-state-"
#let acros = state("acronyms", none)

#let init-acronyms(acronyms) = {
  acros.update(acronyms)
}

// Display acronym
#let display(acr, text) = {
  link(label(acr), text)
}

// Display acronym in short form.
#let acrs(acr, plural: false) = {
  if plural { display(acr, acr + "s") } else { display(acr, acr) }
}
// Display acronym in short plural form
#let acrspl(acr) = { acrs(acr, plural: true) }

// Display acronym in long form.
#let acrl(acr, plural: false) = {
  acros.display(
    acronyms => {
      let def = acronyms.at(acr)
      assert(type(def) == "string")
      if plural {
        display(acr, def + "s")
      } else {
        display(acr, def)
      }
    },
  )
}

// Display acronym in long plural form.
#let acrlpl(acr) = { acrl(acr, plural: true) }

// Display acronym for the first time.
#let acrf(acr, plural: false) = {
  if plural {
    display(acr, [#acrlpl(acr) (#acr\s)])
  } else {
    display(acr, [#acrl(acr) (#acr)])
  }
  state(prefix + acr, false).update(true)
}

// Display acronym in plural form for the first time.
#let acrfpl(acr) = { acrf(acr, plural: true) }

// Display acronym. Expands it if used for the first time.
#let acr(acr, plural: false) = {
  state(prefix + acr, false).display(seen => {
    if seen {
      if plural { acrspl(acr) } else { acrs(acr) }
    } else {
      if plural { acrfpl(acr) } else { acrf(acr) }
    }
  })
}

// Display acronym in the plural form. Expands it if used for the first time.
#let acrpl(acronym) = { acr(acronym, plural: true) }

// Print an index of all the acronyms and their definitions.
#let list-of-acronyms(
  title: "List of Acronyms", delimiter: none, acr-col-size: 20%, level: 1, outlined: false,
) = {
  context if acros.get() != none {
    heading(level: level, outlined: outlined, numbering: none)[#title]
    acros.display(
      acronyms=>{
        for acr in acronyms.keys() {
          table(
            columns: (acr-col-size, 100% - acr-col-size), stroke: none, inset: 0pt, [*#acr#label(acr)#delimiter*], [#acrl(acr)],
          )
        }
      },
    )
  }
}

#let in-outline = state("in-outline", false)

// Display long caption in figure and short caption in list of figures
#let captions(long, short) = context if in-outline.get() { short } else { long }

#let listing(caption: none, label: none, body) = [
  // show line numbers
  #show raw.where(block: true): it => {
    set par(justify: false)
    show raw.line: it => {
      text(fill: gray)[#if it.number < 10 { text(" ") }#it.number]
      h(1em)
      it.body
    }
    box(width: 100%, align(left, it))
  }
  #figure(
    box(body, stroke: 0pt, radius: 5pt, inset: 10pt, fill: white.darken(3%)),
    caption: caption, kind: "listing", supplement: [Listing],
  )
  #label
]

// thesis template
#let thesis(
  title: "Title and\nSubtitle\nof the Thesis",
  author: "Firstname Lastname, BSc",
  curriculum: "Curriculum",
  supervisors: (),
  date: datetime.today(),
  acknowledgments: none,
  abstract: none,
  abstract_de: none,
  acronyms: none,
  body
) = {
  if type(supervisors) != array {
    panic("supervisors must be an array")
  }

  set document(title: title.split("\n").join(" "), author: author)

  set text(size: 11pt, font: "New Computer Modern", hyphenate: false)

  set cite(style: "alphanumeric")

  // title page

  set page(margin: (bottom: 2.75cm))

  set align(center)

  image("logo.svg", width: 20%)

  v(2cm)

  block(text(size: 14pt, author), below: 1.75cm)

  block(text(size: 16pt, weight: "bold", title))

  set align(center + bottom)

  block(par(leading: 9pt, [
    #text(size: 12pt, weight: "bold", "MASTER'S THESIS") \
    #text("to achieve the university degree of\nDiplom-Ingenieur") \
    #text("Master's degree programme: " + curriculum)    
  ]))

  v(1cm)

  block(text(size: 10pt, "submitted to"))
  block(text(weight: "bold", "Graz University of Technology"))
  v(1.1cm)

  block(text(size: 10pt, weight: "bold", "Supervisor" + if supervisors.len() > 1 { "s" }))
  text(size: 10pt, supervisors.join("\n"))

  block(text(size: 10pt, "Institute of Applied Information Processing and Communications"), below: 1.75cm)

  box(text(size: 8pt, [Graz, #date.display("[month repr:long] [year]")],))

  // style rules

  set align(top + left)

  set page(margin: (left: 3cm, right: 3cm, top: 3.7cm, bottom: 5.6cm))

  set par(justify: true, leading: 0.6em)

  set block(below: 16pt)

  set math.equation(numbering: "(1.1)")

  set figure(gap: 15pt)

  set enum(indent: 1em, numbering: "1)a)i)")

  set list(indent: 1em)

  set heading(numbering: "1.1 ")

  set page(header: context {
    // find heading of level 1 on current page
    let chapter = query(heading.where(level: 1), here()).find(h => h.location().page() == here().page())
    // if not chapter begin print current chapter in header
    if chapter == none {
      let elems = query(selector(heading.where(level: 1)).before(here()))
      let counter = counter(heading.where(level: 1))
      if elems.len() != 0 {
        if counter.get().first() == 0 or elems.last().body == [Bibliography] {
          // dont print chapter + counter for outline
          align(center, text(style: "italic", elems.last().body))
        } else {
          align(center, text(style: "italic", "Chapter " + counter.display("1") + " " + elems.last().body))
        }
      }
      v(-.25cm)
    }
  })

  // set ref of level 1 heading to Chapter
  show heading.where(level: 1): set heading(supplement: [Chapter])

  show heading.where(level: 1): it => {
    pagebreak()
    v(2cm)
    let count = counter(heading).get()
    if it.body != [Bibliography] and count.first() > 0 {
      par(leading: 22pt, text(size: 20pt,  "Chapter " + counter(heading).display("1") + linebreak() + it.body))
    } else {
      text(size: 20pt, it)
    }
    v(25pt)
  }

  show heading.where(level: 2): it => {
    v(10pt)
    text(size: 14pt, it)
    v(10pt)
  }

  show heading.where(level: 3): it => {
    v(8pt)
    text(size: 12pt, it)
    v(8pt)
  }

  show heading.where(level: 4): it => {
    v(8pt)
    text(size: 11pt, it.body)
    v(8pt)
  }

  pagebreak()

  // affidavit
  
  align(horizon)[
    #align(center, text(size: 12pt, weight: "bold", "AFFIDAVIT"))
    #v(0.5cm)

    #block(inset: (left: 1cm, right: 1cm))[
      I declare that I have authored this thesis independently, that I have not used other than the declared sources/resources, and that I have explicitly indicated all material which has been quoted either literally or by content from the sources used.
      The text document uploaded to TUGRAZonline is identical to
      the present master’s thesis.

      #v(2.5cm)

      #line(length: 100%, stroke: .5pt)
      #v(-.5cm)
      #align(center, text(size: 8pt, "Date, Signature"))
    ]
  ]

  set page(numbering: "i")

  init-acronyms(acronyms)

  // acknowledgements

  heading(level: 1, outlined: false, numbering: none, "Acknowledgements")

  acknowledgments

  // abstract 

  heading(level: 1, outlined: false, numbering: none, "Abstract")

  abstract

  heading(level: 1, outlined: false, numbering: none, "Kurzfassung")

  abstract_de
  
  // outline

  in-outline.update(true)
  
  show outline.entry.where(level: 1): it => {
    if it.body != [References] {
      v(14pt, weak: true)
      link(it.element.location(), strong([#it.body #h(1fr) #it.page]))
    } else {
      it
    }
  }

  show outline.entry.where(level: 2): it => {
    link(it.element.location(), [
      #it.body #box(width: 1fr, inset: (right: .4cm), repeat[~.]) #it.page
    ])
  }

  show outline.entry.where(level: 3): it => {
    link(it.element.location(), [
      #it.body #box(width: 1fr, inset: (right: .4cm), repeat[~.]) #it.page
    ])
  }

  outline(indent: auto, depth: 3)

  // list of figures
  
  context if query(figure.where(kind: image)).len() > 0 {    
    show outline.entry: it => {
      link(it.element.location(), [
        #it.body #box(width: 1fr, inset: (right: .4cm), repeat[~.]) #it.page
      ])
    }
    outline(title: "List of Figures", target: figure.where(kind: image))
  }

  // list of tables

  context if query(figure.where(kind: table)).len() > 0 {    
    show outline.entry: it => {
      link(it.element.location(), [
        #it.body #box(width: 1fr, inset: (right: .4cm), repeat[~.]) #it.page
      ])
    }
    outline(title: "List of Tables", target: figure.where(kind: table))
  }

  // list of listings

  context if query(figure.where(kind: "listing")).len() > 0 {    
    show outline.entry: it => {
      link(it.element.location(), [
        #it.body #box(width: 1fr, inset: (right: .4cm), repeat[~.]) #it.page
      ])
    }
    outline(title: "List of Listings", target: figure.where(kind: "listing"))
  }

  list-of-acronyms()

  in-outline.update(false)

  set page(numbering: "1")
  counter(page).update(1)

  body
}
