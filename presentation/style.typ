#import "@preview/polylux:0.3.1": *

// Consider using:
// #set text(font: "Fira Sans", weight: "light", size: 20pt)
// #show math.equation: set text(font: "Fira Math")
// #set strong(delta: 100)
// #set par(justify: true)

#let m-dark-gray = rgb("#1A1A1A")
#let m-red = rgb("#F70146")
#let m-extra-light-red = rgb("#e0c0c5")
#let m-extra-light-gray = white.darken(2%)
#let m-light-gray = rgb("#dfdfdf")

#let m-footer = state("m-footer", [])
#let m-page-progress-bar = state("m-page-progress-bar", [])

#let m-cell = block.with(
  width: 100%,
  height: 100%,
  above: 0pt,
  below: 0pt,
  breakable: false
)

#let m-progress-bar = utils.polylux-progress( ratio => {
  grid(
    columns: (ratio * 100%, 1fr),
    m-cell(fill: m-red),
    m-cell(fill: m-extra-light-red)
  )
})

#let tugraz-theme(
  aspect-ratio: "16-9",
  footer: [],
  progress-bar: true,
  body
) = {
  set page(
    paper: "presentation-" + aspect-ratio,
    margin: 0em,
    header: none,
    footer: none,
  )
  set list(marker: (text(fill: m-red, sym.square.filled), text(fill: black, sym.square.filled), text(fill: gray, sym.square.filled)))
  m-footer.update(footer)
  if progress-bar {
    m-page-progress-bar.update(m-progress-bar)

  }

  show list.item: it => {
    v(.5cm)
    it
  }

  set table(
    inset: 10pt,
    gutter: 2pt,
    stroke: none,
    fill: (_, y) => if y == 0 { m-red } else if calc.odd(y) { m-light-gray }
  )

  set cite(style: "alphanumeric")

  set bibliography(title: none)

  body
}

#let title-slide(
  title: [],
  subtitle: none,
  author: none,
  date: none,
  extra: none,
) = {
  let content = {
    set text(fill: m-dark-gray)
    set align(horizon)
    place(top + right, pad(30%, image("./logo.svg", format: "svg", width: 20%)))
    block(width: 100%, inset: 2em, {
      text(size: 1.8em, strong(title), weight: "regular", fill: m-red)
      if subtitle != none {
        linebreak()
        linebreak()
        text(size: 0.8em, subtitle)
      }
      line(length: 100%, stroke: .05em + m-red)
      set text(size: .8em)
      if author != none {
        block(spacing: 1em, text(weight: "medium", author))
      }
      if date != none {
        block(spacing: 1em, date)
      }
      set text(size: .8em)
      if extra != none {
        block(spacing: 1em, extra)
      }
    
    })
  }

  logic.polylux-slide(content)
}

#let slide(title: none, body) = {
  let header = {
    set align(top)
    if title != none {
      show: m-cell.with(fill: m-dark-gray, inset: 1em)
      set align(horizon)
      set text(fill: m-extra-light-gray, size: 1.2em)
      strong(title)
      h(1fr)
      box(pad(bottom: .75em, text(size: .5em, "www.tugraz.at", weight: "medium")))
      box(pad(left: .2em, bottom: .75em, square(fill: m-red, size: .3em)))
    } else { 
      h(1fr)
      box(pad(bottom: .75em, text(size: .5em, "www.tugraz.at", weight: "medium")))
      box(pad(left: .2em, bottom: .75em, square(fill: m-red, size: .3em)))
    }
  }

  let footer = {
    set text(size: 0.7em)
    show: m-cell.with(fill: m-light-gray)
    set align(horizon)

    box(align(left+top, square(height: 100%, fill: m-red, align(horizon+center, text(fill: m-extra-light-gray, weight: "regular", size: .9em, logic.logical-slide.display())))))
  
    h(1fr)
    box(height: 100%, pad(1.5em, text(fill: m-dark-gray, size: .9em, m-footer.display())))
    place(bottom, block(height: 2pt, width: 100%, m-page-progress-bar.display()))
  }

  set page(
    header: header,
    footer: footer,
    margin: (top: 3em, bottom: 2em),
  )

  let content = {
    show: align.with(horizon)
    show: pad.with(left: 2em, right: 2em, top: 2em)
    set text(fill: m-dark-gray)
    v(-2cm)
    body 
  }

  logic.polylux-slide(content, max-repetitions: 15)
}

#let new-section-slide(name) = {
  let content = {
    utils.register-section(name)
    set align(horizon)
    show: pad.with(20%)
    set text(size: 1.5em)
    name
    block(height: 2pt, width: 100%, spacing: 0pt, m-progress-bar)
  }
  logic.polylux-slide(content)
}

#let focus-slide(body) = {
  set page(fill: m-dark-gray, margin: 2em)
  set text(fill: m-extra-light-gray, size: 1.5em)
  logic.polylux-slide(align(horizon + center, body))
}

#let alert = text.with(fill: m-red)

#let numbering-func(..nums) = {
  box(
    square(fill: m-red, height: 1.2em,
      align(center, text(fill: m-extra-light-gray, weight: "medium",
        nums.pos().map(str).join("."))
      )
    )
  )
}

#let m-outline = utils.polylux-outline(enum-args: (tight: false, numbering: numbering-func))

  
