#import "./style.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#show: tugraz-theme.with(
  footer: [Fabian Gruber],
  progress-bar: true
)

#enable-handout-mode(true)
#set text(font: "Fira Sans", weight: "regular", size: 20pt)
// #show math.equation: set text(font: "Fira Math")
#set strong(delta: 100)
#set par(justify: false)

#title-slide(
  author: [Fabian Gruber],
  title: [riscMPC],
  subtitle: [General-Purpose Multi-Party Computation from RISC-V Assembly],
  date: [September 06, 2024],
)

#let arith(x) = [#sym.bracket.l #x #sym.bracket.r]
#let bin(x) = [#sym.angle.l #x #sym.angle.r]
#let xor = sym.plus.circle

#let listing(caption: none, label: none, body) = [
  // show line numbers
  #show raw.where(block: true): it => {
    set par(justify: false)
    show raw.line: it => {
      text(fill: gray)[#it.number]
      h(1em)
      it.body
    }
    box(width: 100%, align(left, it))
  }
  #box(body, stroke: 0pt, radius: 5pt, inset: 10pt, fill: white.darken(3%))
]

#slide(title: "Outline")[
  #m-outline
]

// ========== Introduction ========== 

#new-section-slide("Introduction")

#slide(title: "Motivation")[
  #line-by-line(mode: "transparent")[
    - Rising privacy concerns increase importance of MPC
    - High complexity and performance costs slow down adoption
    - Integration should be faster and easier
  ]
]

#slide(title: "Goal")[
  #line-by-line(mode: "transparent")[
    - Map RISC-V instructions to MPC operations
    - Virtual Machine (VM) abstracts MPC away
    - Base 64-bit instruction set + Important extensions
    - Users only have to care about inputs
  ]
]

// ========== Background ========== 

#new-section-slide("Background")

#slide(title: "Multi-Party Computation")[
  #line-by-line(mode: "transparent")[
    - Cryptographic protocols that allow secret computation
    - Inputs can be secret or public
    - Parties learn only results
    - Operate on shares (Additive, Shamir @shamir1979share)
  ]
]

#slide(title: "Multi-Party Computation")[
  #line-by-line(mode: "transparent")[
    - Different protocols for different numbers of parties
    - Security assumptions
      - Semi-honest/malicious adversary
      - Honest/dishonest majority
    - Used for Private Set Intersection, Statistics, Privacy-Preserving Machine Learning
  ]
]

#slide(title: "Share Conversions")[
  #line-by-line(mode: "transparent")[
    - Mixed protocols allow efficient computation
    - E.g. ABY uses (A)rithmentic, (B)inary and (Y)ao shares @demmler2015aby
    - We implemented A2B and B2A conversions
      - Arithmetic share: $arith(x)$
      - Binary share: $bin(x)$
  ]
  #pdfpc.speaker-note(
    ```
    arith shares for add, mul, .. bin shares for xor, and, ..
    ```
  )
]

// #slide(title: "Oblivious Transfer")[
//   #side-by-side(columns: (1fr, 1.5fr))[
//     #line-by-line(mode: "transparent")[
//       - Important cryptographic primitive
//       - Better performance with OT extension
//         - Small number of base OTs
//         - Cheap extend to more
//     ]
//   ][
//     #diagram(node-corner-radius: 10pt, node-defocus: -6, edge-stroke: 1.5pt, {
//       node((0,0), width: 3cm, height: 1.5cm, text(size: 16pt, "Sender"), name: <S>)
//       node((1.5,0), width: 3.5cm, height: 2cm, text(size: 16pt, "1-out-of-2 OT"), name: <OT>, stroke: 2pt)
//       node((3,0), width: 3cm, height: 1.5cm, text(size: 16pt, "Receiver"), name: <R>)
//       edge(<S>, <OT>, "-|>", $(M_0, M_1)$, label-side: right)
//       edge(<R>, <OT>, "-|>", $c$, label-side: right, shift: -10pt)
//       edge(<OT>, <R>, "-|>", $M_c$, label-side: right, shift: -10pt)
//     })
//   ]
// ]

#slide(title: "RISC vs CISC")[
  #line-by-line(mode: "transparent")[
    - (R)educed (I)nstruction (S)et (C)omputer
    - (C)omplex (I)nstruction (S)et (C)omputer
    - Less and simpler vs. more and complicated instructions
  ]
]

// #slide(title: "RISC vs CISC")[
//   #side-by-side[
//     #align(top + center)[
//       CISC
//       ```asm
//       mul eax, 0x10, 0xA0
//       ```
//     ]
//   ][
//     #align(top + center)[
//       RISC
//       ```asm
//       ld a0, 0x10
//       ld a1, 0xA0
//       mul a0, a0, a1
//       ```
//     ]
//   ]
// ]

#slide(title: "RISC-V")[
  #side-by-side(columns: (1.5fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Free and open-source RISC architecture
      - Base integer ISAs RV32I and RV64I
      - 31 general-purpose registers `x1-31`
      - Additional instruction extensions
    ]
  ][
    #image("figures/riscv_logo.png", width: 75%)
  ]
]

#slide(title: "Extensions")[
  #align(center, image("figures/extensions.png", width: 50%))
  #pdfpc.speaker-note(
    ```
    M, F/D, V
    ```
  )
]

#slide(title: "Registers")[
  #align(center, image("figures/registers.png", width: 50%))
  #pdfpc.speaker-note(
    ```
    abi names of arg regs, zero reg
    ```
  )
]

// #slide(title: "Calling Convention")[
//   #side-by-side[
//     #line-by-line(mode: "transparent")[
//       - Arguments passed via registers `a0-7`
//       - Return values are in `a0`, `a1`
//       - Structs/arrays passed via pointers
//     ]
//   ][
//     #listing(
//       ```rust
//       fn foo(a0: u64, a1: u64) -> u64 {
//         a0 + a1
//       }
//       ```
//     )

//     #listing(
//       ```asm
//       foo:
//         add     a0, a0, a1
//         ret
//       ```
//     )
//   ]
// ]

// ========== riscMPC ========== 

#new-section-slide("riscMPC")

#slide(title: "riscMPC Virtual Machine")[
  #side-by-side(columns: (2fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - riscMPC implements a 2-Party semi-honest MPC setting
      - Both parties execute RISC-V assembly instructions
      - Arguments can be secret or public
    ]
  ][
    #diagram(node-stroke: 2pt, node-corner-radius: 10pt, node-defocus: -6, edge-stroke: 1.5pt, {
      node((-0.5,-1), width: 3cm, height: 1.5cm, text(size: 16pt, "Program"), name: <P>)
      node((0.5,-1), width: 3cm, height: 1.5cm, text(size: 16pt, "Inputs"), name: <I>)
      edge(<P>, <VM>, "-|>")
      edge(<I>, <VM>, "-|>")
      node((0,0), width: 4cm, height: 2.5cm, fill: m-red, text(fill: white, "riscMPC VM"), name: <VM>)
      edge("-|>")
      node((0,1), width: 3cm, height: 1.5cm, text(size: 16pt, "Outputs"))
    })
  ]
]

#slide(title: "riscMPC Virtual Machine")[
  #table(
    columns: 3,
    align: (left, center, center),
    [#text(fill: white)[*Features*]], [#text(fill: white)[*Project*]], [#text(fill: white)[*Thesis*]],
    [RV64IM (base 64-bit instructions + mul/div)], [$checkmark$], [$checkmark$],
    [Double precision floating-point], [$times$], [$checkmark$],
    [Vector operations], [$times$], [$checkmark^*$],
    [Fast offline phase (OT extension)], [$times$], [$checkmark$],
  )
]

#slide(title: "Data Types")[
  #side-by-side[
    - Share enum represents arithmetic or binary shares
    
    #listing(
      ```rust
      enum Share {
        Arithmetic(u64),
        Binary(u64),
      }
      ```
    )
  ][
    #align(center)[
      #diagram(node-outset: 5pt, {
        node((0,0), $arith(x)$)
        edge("-|>", bend: 70deg, label: `a2b`)
        edge("<|-", bend: -70deg, label: `b2a`)
        node((1,1), $bin(x)$)
      })
    ]
  ]
]

#slide(title: "Data Types")[
  #side-by-side(gutter: 60pt)[
    - Integer enum represents secret or public integers

    #listing(
      ```rust
      enum Integer {
        Secret(Share),
        Public(u64),
      }
      ```
    )

  ][
    - Float enum represents secret or public floating-point numbers

    #listing(
      ```rust
      enum Float {
        Secret(u64),
        Public(f64),
      }
      ```
    )
  ]
  #pdfpc.speaker-note(
    ```
    secret floats use fixed-point encoded values, arith shares
    ```
  )
]

// #slide(title: "Fixed-Point Encoding")[
//   #line-by-line(mode: "transparent")[
//     - Additive sharing only works in $ZZ_(2^l)$ or $FF_p$
//     - What about real number $attach(limits(x), t: tilde) in RR$?
//     - Encode to integer with scaling factor
//       $
//         x = floor(attach(limits(x), t: tilde) dot 2^k)
//       $
//     - Multiplication of 2 fixed-point numbers has factor $2^(2k)$

//       $->$ divide by $2^k$
//   ]
// ]

#slide(title: "Instruction Examples")[
  #table(
    columns: 2,
    [#text(fill: white)[*Instruction*]], [#text(fill: white)[*Description*]],
    [``` add rd, rs1, rs2```], [Add `rs1` and `rs2` store in `rd`],
    [``` xor rd, rs1, rs2```], [Xor `rs1` and `rs2` store in `rd`],
    [``` mul rd, rs1, rs2```], [Multiply `rs1` and `rs2` store in `rd`],
    [``` blt rs1, rs2, label```], [Branch to `label` if `rs1 < rs2`],
    [``` fsqrt rd, rs1```], [Square root of `rs1` store in `rd`],
  )
]

#slide(title: "Addition")[
  #side-by-side(columns: (2fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Parties locally compute $arith("rs1") + arith("rs2")$
      - Public operand 1 party computes $arith("rs1") + "rs2"$
    ]
  ][
  #table(
    columns: 2,
    [#text(fill: white)[*Comm*]], [#text(fill: white)[*Setup*]],
    [-], [-],
  )
  ]
]

#slide(title: "Binary XOR")[
  #side-by-side(columns: (2fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Parties locally compute $bin("rs1") xor bin("rs2")$
      - Public operand 1 party computes $bin("rs1") xor "rs2"$
    ]
  ][
  #table(
    columns: 2,
    [#text(fill: white)[*Comm*]], [#text(fill: white)[*Setup*]],
    [-], [-],
  )
  ]
]

#slide(title: "Multiplication")[
  #side-by-side(columns: (2fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Naive approach fails
      - Instead use Mult. Triple $(arith(a), arith(b), arith(c))$ @beaver1992efficient
        $
          arith(d) &= arith("rs1") - arith(a) \
          arith(e) &= arith("rs2") - arith(b) \
          arith("res") &= arith(c) + d arith("rs2") + e arith("rs1") + d e
        $
      - Public operand all parties computes $"rs2" arith("rs1")$
    ]
  ][
  #table(
    columns: 2,
    [#text(fill: white)[*Comm*]], [#text(fill: white)[*Setup*]],
    [2 $times$ 64-bit], [1 MT],
  )
  ]
]

#slide(title: "Branch if Less-Than")[
  #side-by-side(columns: (2fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Secretly compute sign-bit:
        $
          arith(s) &= arith("rs1") - arith("rs2") \
          bin(s) &= "A2B"(arith(s)) \
          bin("sign-bit") &= bin(s) >> 63
        $
      - Open sign-bit, take branch if it's 1 (negative difference $-> "rs1" < "rs2"$)
      - A2B conversion costs 13 AND triples
    ]
  ][
  #table(
    columns: 2,
    [#text(fill: white)[*Comm*]], [#text(fill: white)[*Setup*]],
    [64-bit], [13 ATs],
  )
  ]
]

#slide(title: "Square Root")[
  #side-by-side(columns: (2fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Numerical approximation with Newton's method
      - Sqrt includes div by secret $->$ inv sqrt instead:
        $
          y_(n+1) = 1/2 y_n (3 - x y_n^2)
        $
      - After 3 Newton's iterations
        $
          sqrt(x) = x 1/sqrt(x)
        $ 
    ]
  ][
  #table(
    columns: 2,
    [#text(fill: white)[*Comm*]], [#text(fill: white)[*Setup*]],
    [10 $times$ 2 $times$ 64-bit], [10 MTs],
  )
  ]
  #pdfpc.speaker-note(
    ```
    # num MTs
    10 = (9 for 3 mul per iter and 3 iter) + (1 for mul inv sqrt)
    # initial approx
    needs inital approx to work, also uses MTs
    ```
  )
]

// ========== Results ==========

#new-section-slide("Results")

#slide(title: "Usage")[
  #side-by-side(columns: (1fr, 3fr))[
    #line-by-line(mode: "transparent")[
      - Parties set inputs
      - Execute program
      - Open result
    ]
  ][
    #listing(
      ```rust
      // parse RISC-V assembly
      let program = "add a0, a0, a1".parse()?;
      // create party with builder pattern
      let mut party = PartyBuilder::new(PARTY_0, ch)
          .register_u64(XRegister::x10, Integer::Secret(2))
          .register_u64(XRegister::x11, Integer::Secret(3))
          .build()?;
      // execute add function
      party.execute(&program)?;
      // open result in return value register
      let res = party.register_u64(XRegister::x10)?;      
      ```
    )
  ]
]

#slide(title: "Example: Mean Salary")[
  #side-by-side(columns: (1fr, 2fr))[
    #line-by-line(mode: "transparent")[
      - Privacy-preserving statistics
      - Compute mean without revealing salaries to other party
    ]
  ][
    #listing(
      ```rust
      fn mean(sal0: &[u64], sal1: &[u64]) -> u64 {
        let sum = 
          sal0.iter().sum::<u64>() +
          sal1.iter().sum::<u64>();
        sum / (sal0.len() + sal1.len()) as u64
      }
      ```
    )
  ]
]

// #slide(title: "Example: Mean Salary")[
//   #align(center, image("figures/mean_salary.png", width: 60%))
// ]

#slide(title: "Example: Private Set Intersection")[
  #side-by-side(columns: (1.5fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Compute intersection without revealing set to other party
      - Used in contact discovery
      - Different solutions exist
    ]
  ][
    #diagram(node-stroke: 2pt, node-shape: circle, {
      node((0, 0), pad(right: 40pt, text(size: 16pt, "?")), radius: 2.5cm, stroke: red)
      node((0.5, 0), pad(left: 40pt, text(size: 16pt, "?")), radius: 2.5cm, stroke:  blue)
      node((0.25, 0), [A #sym.sect B], stroke: none)
    })
  ]
]

#slide(title: "Example: Private Set Intersection")[
  #align(center, image("figures/psi_comparison.png", width: 60%))
]

#slide(title: "Example: Ascon AEAD")[
  #side-by-side(columns: (1.5fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - Ascon round needs XOR, NOT, AND, ROT
      - XOR and NOT are free
      - 5 AND + 10 OR (in ROT) $->$ 15 Beaver triples
    ]
  ][
    #set text(size: 10pt)
    #listing(
      ```rust
      pub fn round(x: [u64; 5], c: u64) -> [u64; 5] {
          // S-box layer
          let x0 = x[0] ^ x[4];
          let x2 = x[2] ^ x[1] ^ c; // with round constant
          let x4 = x[4] ^ x[3];

          let tx0 = x0 ^ (!x[1] & x2);
          let tx1 = x[1] ^ (!x2 & x[3]);
          let tx2 = x2 ^ (!x[3] & x4);
          let tx3 = x[3] ^ (!x4 & x0);
          let tx4 = x4 ^ (!x0 & x[1]);
          let tx1 = tx1 ^ tx0;
          let tx3 = tx3 ^ tx2;
          let tx0 = tx0 ^ tx4;

          // linear layer
          let x0 = tx0 ^ tx0.rotate_right(9);
          let x1 = tx1 ^ tx1.rotate_right(22);
          let x2 = tx2 ^ tx2.rotate_right(5);
          let x3 = tx3 ^ tx3.rotate_right(7);
          let x4 = tx4 ^ tx4.rotate_right(34);
          [
              tx0 ^ x0.rotate_right(19),
              tx1 ^ x1.rotate_right(39),
              !(tx2 ^ x2.rotate_right(1)),
              tx3 ^ x3.rotate_right(10),
              tx4 ^ x4.rotate_right(7),
          ]
      }
      ```
    )
  ]
]

#slide(title: "Example: Ascon AEAD")[
  #side-by-side(columns: (1fr, 1.25fr))[
    #line-by-line(mode: "transparent")[
      - Use pre-shared `key`
      - Party 0 inputs `pt` and get `ct` + `tag`
      - Party 1 doesn't learn `pt` and `ct`
      - Under $1"ms"$ per block
    ]
  ][
    #set text(size: 11pt)
    #listing(
      ```rust
      let mut party = PartyBuilder::new(PARTY_0, ch0)
        .register_u64(XRegister::x11, Integer::Public(key_addr))
        .register_u64(XRegister::x13, Integer::Public(pt_addr))
        .register_u64(XRegister::x14, Integer::Public(pt_len))
        .address_range_shared_u64(
            key_addr,
            key.iter().map(|x| Integer::Secret(Share::Binary(*x))).collect(),
        )?
        .address_range_u64(
            pt_addr,
            pt.iter().map(|x| Integer::Secret(Share::Binary(*x))).collect(),
        )?
        .n_and_triples(15 * 12 * 2 + 15 * 6 * pt_len)
        .build()?;
      party.execute(
          &program.parse::<Program>()?.with_entry("encrypt_inplace")?
      )?;
      let ct = party.address_range_u64_for(
          pt_addr..pt_addr + pt_len * U64_BYTES, PARTY_0
      )?;
      let tag = party.address_range_u64_for(
          key_addr..key_addr + key_len * U64_BYTES, PARTY_0
      )?;
      ```
    )
  ]
]

// #slide(title: "Example: Ascon AEAD")[
//   #align(center, image("figures/ascon_aead_perf.png", width: 60%))
// ]

#slide(title: "Example: MNIST Digit Recognition")[
  #side-by-side(columns: (1fr, 1fr))[
    #line-by-line(mode: "transparent")[
      - One party provides trained model, other provides image
      - Inference happens in MPC
      - "1" with 95.5% in 2.86s
      - 100k Multiplication triples, 10k Binary triples
    ]
  ][
    #align(center, figure(image("figures/digit.png", width: 60%), caption: [28x28 test image], numbering: none))
  ]
  #pdfpc.speaker-note(
    ```
    # network
    28x28 (784) - 100 - 10
    # activation
    linear sigmoid approx
    ```
  )
]

#slide(title: "Example: Vectorized Multiplication")[
  #align(center, image("figures/mul_vs_vmul.png", width: 60%))
]

// #slide(title: "Benchmark: Network Latency")[
//   #align(center, image("figures/mul_latency.png", width: 60%))
// ]

// ========== Conclusion ========== 

#new-section-slide("Conclusion")

#slide(title: "Conclusion")[
  #line-by-line(mode: "transparent")[
    - Fast development and easy to use
    - RV64IM compatible
      - Support for 64-bit floating-point numbers
      - Limited support for vectorized instructions
    - Good performance
      - Fast online phase
      - Fast setup phase with OT extension
  ]
]

#slide(title: "")[
  #align(center, text(size: 40pt, "Questions?"))
]

#slide(title: "Bibliography")[
  #bibliography("slides.bib")
]
