//#import "@preview/colorful-boxes:1.4.2": *
#import "@preview/showybox:2.0.4": showybox
#import "@preview/fletcher:0.5.5": node, edge, diagram
#import "template/definitions.typ": *
#import "@preview/peace-of-posters:0.5.2" as pop
#import "@preview/cetz:0.3.2"
#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm

//#bibliography("references/ref.bib",style: "apa")

#let uni-cp = (
    "body-box-args": (
        inset: 0.6em,
        width: 100%,
    ),
    "body-text-args": (:),
    "heading-box-args": (
        inset: 0.6em,
        width: 100%,
        fill: rgb("#2596be"),
        stroke: rgb("#2596be"),
    ),
    "heading-text-args": (
        fill: white,
    ),
)

#set cite(form: "prose")
#set page("a0", margin: 1cm)
#pop.set-poster-layout(pop.layout-a1)
#pop.set-theme(uni-cp)
#set text(size: pop.layout-a0.at("body-size"))
#let box-spacing = 1em
#set columns(gutter: box-spacing)
#set block(spacing: box-spacing)
#pop.update-poster-layout(spacing: box-spacing)

#show ref: it => [#text(fill: blue)[#it]]
#show table.cell.where(y: 0): strong
#set table(
  stroke: (x, y) => if y == 0 {
    (bottom: 0.7pt + black)
  },
  align: (x, y) => (
    if x > 0 { center }
    else { left }
  )
)

#pop.title-box(
    "A New Iterated Conditional Expectations Estimator for Longitudinal Causal Effects in Continuous Time",
    authors: [
        Johan Sebastian Ohlendorff#super("1"),
        Anders Munch#super("1"),
        and Thomas Alexander Gerds#super("1"),
    ],
    institutes: [#super("1") Section of Biostatistics, University of Copenhagen],
    logo: scale(image("ku_logo.png"), 120%),
    spacing: 8em
)

#columns(2,[
  #pop.column-box(heading: "Motivation")[
      - In medical research, the estimation of causal effects of treatments over time is often of interest.
      //- The potential outcome framework @robins1986 allows one to estimate the causal effect of multiple time point interventions in discrete time.
      - Continuous-time inference allows for data that is more closely aligned with the data collection process (@fig:longitudinaldata). Moreover, discrete time approaches usually
        require the discretization of time, leading to a loss of information.
      - There is a scarcity of (applied) literature on the estimation of longitudinal causal effects in continuous time.
        @rytgaardContinuoustimeTargetedMinimum2022 considered a targeted minimum-loss based estimator based on
        iterated conditional expectations (@fig:timegridrytgaard) for estimating causal effects flexibly.// with the efficient influence curve @bickel1993efficient.
        However, this estimator quickly becomes intractable.
      - We propose a new feasible iterated conditional expectations estimator (@fig:eventgrid) for the estimation of longitudinal causal effects in continuous time.
        #figure(cetz.canvas(length: 1.8cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 4),
    stroke: (thickness: 2pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .8,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 8pt)
  )
  
  let time_grid(cord_start,cord_end, time_values, inc: 0.1, anchor: "north") = {
      // Main axis line
      set-style(mark: (end: ">"))
      line(cord_start, cord_end)
      set-style(mark: none)

      // General time line
      let early_stop = cord_end.first() - 1/10 * cord_end.first()
      let t_grid = frange(cord_start.first()+inc,early_stop - inc, inc)
      
      // Start line
      line((cord_start.first(), -2*inc+cord_start.last()), (cord_start.first(), 2*inc+cord_start.last()), name:"lstart")
      content("lstart.start", [], anchor: "east")
      
      // End line
      line((early_stop - inc, -2*inc+cord_end.last()), (early_stop - inc, 2*inc+cord_end.last()), name: "lend")
      content("lend.start", [#text(size: 12pt)[$tau_"end"$]],anchor: "north")

      // Draw grid
      for i in t_grid {
        line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
      }

      // Deal with the marks/events
      let event_list = ()
      for t in range(0, time_values.len()) {
        event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
        //content(v.name + ".start", [#v.mformat], anchor: anchor)
      }
    }
    let eventfun(x, where: "start", anchor: "north",start_y: 0)={
      let event_list = ()
      for t in range(0, x.len()) {
        event_list.push((name: "v" + str(t), value: x.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value, -1.5+start_y), (v.value, 1.5+start_y), stroke: blue,name: v.name)
        content(v.name + "." + where, [#text(size: 12pt)[#v.mformat]], anchor: anchor)
      }
    }

    rect((0,1.5), (2.8,-1.5),fill:aqua,stroke:none)
    let grid1 = (2.5,4.4,6.4)
    // Deal with the marks/events
    eventfun(grid1)
    
    let grid2 = (1,1.7, 2.3,2.8)
    eventfun(grid2, where: "end", anchor: "south")
    
    group({time_grid((0,-1),(10,-1), grid1,inc: 0.1,anchor: "south")})
    group({time_grid((0,1),(10,1), grid2)})
}), caption:  [The figure illustrates the sequential regression approach
    given in @rytgaardContinuoustimeTargetedMinimum2022 for two observations.
],) <fig:timegridrytgaard>

      #figure(cetz.canvas(length: 1.8cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 4),
    stroke: (thickness: 2pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .8,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 8pt)
  )
  
  let time_grid(cord_start,cord_end, time_values, inc: 0.1, anchor: "north") = {
      // Main axis line
      set-style(mark: (end: ">"))
      line(cord_start, cord_end)
      set-style(mark: none)

      // General time line
      let early_stop = cord_end.first() - 1/10 * cord_end.first()
      let t_grid = frange(cord_start.first()+inc,early_stop - inc, inc)
      
      // Start line
      line((cord_start.first(), -2*inc+cord_start.last()), (cord_start.first(), 2*inc+cord_start.last()), name:"lstart")
      content("lstart.start", [], anchor: "east")
      
      // End line
      line((early_stop - inc, -2*inc+cord_end.last()), (early_stop - inc, 2*inc+cord_end.last()), name: "lend")
      content("lend.start", [#text(size: 12pt)[$tau_"end"$]],anchor: "north")

      // Draw grid
      for i in t_grid {
        line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
      }

      // Deal with the marks/events
      let event_list = ()
      for t in range(0, time_values.len()) {
        event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
        content(v.name + ".start", [#text(size: 12pt)[#v.mformat]], anchor: anchor)
      }
    }

          rect((0,1.5), (1.7,0.3),fill:aqua,stroke:none)
    rect((0,-1.7), (4.4,-0.5),fill:aqua,stroke:none)
    let grid1 = (2.5,4.4,6.4)
    // Deal with the marks/events
    
    let grid2 = (1,1.7, 2.3,2.8)
    
    group({time_grid((0,-1),(10,-1), grid1, anchor: "north-east")})
    group({time_grid((0,1),(10,1), grid2, anchor: "north-east")})
}), caption: [The figure illustrates the sequential regression approach
    proposed in this article. 
],) <fig:eventgrid>


      #figure(table(
  columns: (auto, auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
      [id], [time], [event],
  ),
          [1], [3], [side effect],
          [1], [8], [primary event],
          [2], [10], [primary event],
          [3], [2], [side effect],
          [3], [5], [treatment shift],
          [3], [7], [censoring],
          [], [...], []
      ),
        caption: [
            An example of a longitudinal dataset from electronic health records or a clinical trial. Events are registered at irregular/subject-specific time points.
        ]
      ) <fig:longitudinaldata>
  ]

    #pop.column-box(heading: "Setting")[
        Let $(N^a (t), A (t), N^ell (t), L(t), N^y (t), N^d (t), N^c (t))$#footnote[We associate to this process its natural filtration $cal(F)_t$ implicitly defined on a probability space $(Omega, cal(F), P)$.] be a stochastic processes observed in $[0, tauend]$,
        consisting of a counting process for treatment visits, treatment values, a counting process for treatment covariate measurements, covariate values, and counting processes for the primary event, competing event, and censoring, respectively.
        //Furthermore, $Delta A (t) = 0$ ($Delta L (t) = 0$) if $Delta N^a (t)$ ($Delta N^ell (t) = 0$).
        Furthermore, $A (t) in {0, 1}$ and $L (t) in cal(L)$, where $cal(L) subset.eq RR^d$ is a finite set. 
          
          #assumption[
In the time interval $[0, tauend]$ there are at most $K - 1 < oo$ many changes of treatment and
              covariates in total for a single individual.
          ] 
        #assumption[
       The counting processes $N^a$, $N^ell$, $N^y$, $N^d$, and $N^c$ have with probability 1 no jump times in common. 
        ]

        Under these assumptions, the observed data can be written in the form
        $
            O = history(K)
        $
        where
        $
            history(k) = (event(k), Delta_k, treat(k), covariate(k)) or history(k-1) "and" history(0) = (covariate(0), treat(0))
        $
        //and $event(k)$ and $Delta_k in {a, ell, y, d, c}$ are the event time and status indicator for the $k$'th event. 
        #assumption[
            For each $k in {1, dots, K}$,  $event(k) | history(k-1) lt.double m$ #footnote[$m$ is the Lebesgue measure on $RR_+$.], $treat(k) | event(k) = t, Delta_k = a, history(k-1) lt.double nu_a$, and $covariate(k) | event(k) = t, status(k) = ell, history(k-1) lt.double nu_ell$.
        //     We assume that the conditional distributions 
        //     $P(event(k) in dot | history(k-1)) lt.double m$ $P$-a.s., and $P(treat(k) in dot | event(k) = t, Delta_k = a, history(k-1)) lt.double nu_a$ $P$-a.s. and $P(covariate(k) in dot | event(k) = t, status(k) = ell, history(k-1)) lt.double nu_ell$ $P$-a.s., where $m$ is the Lebesgue measure on $RR_+$, $nu_a$ is a measure on $cal(A)$, and $nu_ell$ is a measure on $cal(L)$.
            //] <assumptionabscont>
        ]
    ]

    #pop.column-box(heading: "Target parameter")[
        Let $tilde(T)^(bold(1))_k$ and $tilde(Delta)^(bold(1))_k$ be the counterfactual event time and indicator for the $k$'th had the patient stayed on treatment and initially received treatment (and not been censored).
        Our target parameter $Psi_(tau)^g : cal(M) -> RR$ is the mean interventional potential outcome at time $tau$ given the intervention plan $g$.
 
    $
        Psi_(tau)^g (P) = mean(P) [sum_(k=1)^K bb(1) {tilde(T)^(bold(1))_k <= tau, tilde(Delta)^(bold(1))_k = y}].
    $
]

    #pop.column-box(heading: "Identification")[
        We consider identification conditions in Theorem 3 of @ryalenPotentialOutcomes. These are stated in our present uncensored setting.
        Let $tilde(Y)_t = (bb(1) {tilde(T)^(bold(1))_1 <= t, tilde(Delta)^(bold(1))_1 = y}, dots, bb(1) {tilde(T)^(bold(1))_K <= t, tilde(Delta)^(bold(1))_K = y})$ and $T^a = inf {t > 0 : A(t) != 1}$.
        For each $k in {1, dots, K}$, we need:
        - Consistency:
          $
              bb(1) {tilde(T)^(bold(1))_k <= t, tilde(Delta)^(bold(1))_k = y} bb(1) {T^a > t, A(0) = 1} = bb(1) {T_k <= t, Delta_k = y} bb(1) {T^a > t, A(0) = 1}
          $
          for $t in [0, tauend]$.
        - Exchangeability:
          $
              treat(k) perp (bb(1){tilde(T)^(bold(1))_(k+1) <= t, tilde(D)^(bold(1))_(k+1) = y}, dots, bb(1){tilde(T)^(bold(1))_K <= t, tilde(D)^(bold(1))_K = y}) | status(k) = a, history(k-1)
          $
          (and
          $
              &lambda^a (t | history(k-1) or (tilde(Y)_t)_(t in [0, tauend]) ) \
                  &= lim_(h -> 0) (P(t <= event(k) < t+h, Delta_k = a | event(k) >= t, history(k-1), (tilde(Y)_t)_(t in [0, tauend])))/h
          $
          does not depend on $(tilde(Y)_t)_(t in [0, tauend])$).
        - Positivity: The weights
          $
              w_k (f_(k-1), t_k) = (bb(1) {a_0 = 1}) / ( pi_0 (l_0)) product_(j=1)^(k-1) ( (bb(1) {a_j = 1})  / ( pi_j ( f_(j-1))))^(bb(1) {delta_j = a}) bb(1) {t_1 < dots < t_k}
          $
          fulfill $mean(P) [w_k (history(k-1), event(k))] = 1$. //, where we define $pi_0 (l) = P(A(0) = 1 | L(0) = l_0)$ and $pi_j (f) = P(treat(j) = 1 | Delta_j = a, history(j-1) = f)$.
          #showybox(
  title: "Identification formula", 
  frame: (
    border-color: blue,
    title-color: blue.lighten(30%),
    body-color: blue.lighten(95%),
      footer-color: blue.lighten(80%),
      radius: (top-left: 10pt, bottom-right: 10pt, rest: 0pt)
  )
)[
  Under the assumptions of consistency, exchangeability, and positivity, the target parameter is identified via
        $
            Psi_(tau)^g (P) = mean(P) [sum_(k=1)^K w_k (history(k-1), event(k)) bb(1) {T_k <= tau, Delta_k = y}].
        $
]
        
    ]
    
    #pop.column-box(heading: "Iterated Conditional Expectation Estimator")[
        The form of the efficient influence function (@bickel1993efficient) in this setting suggests the use of a iterated conditional expectations estimator.
        //Moreover, the estimator is more stable than inverse probability weighted estimators.
        Let $S^c (t | history(k))$ be the conditional survival function of the censoring time given the $k$ previous events
        and $cal(F)^(-A)_(event(k))$ denote the history without the treatment process.
      
        

        #showybox(
            title-style: (boxed-style: (:)),
            frame: (
    border-color: blue,
    title-color: blue.lighten(30%),
      footer-color: blue.lighten(80%),
      radius: (top-left: 10pt, bottom-right: 10pt, rest: 0pt)
  ),
      title: "Proposed continuous-time ICE estimator",
        [- For each event point $k = K, K-1, dots, 1$ (starting with $k = K$):
        1. Obtain $hat(S)^c (t | history(k))$ by fitting a cause-specific hazard model for the censoring via the interevent time $S_((k)) = event(k) - event(k-1)$,
           regressing on $history(k-1)$ (among the people who are still at risk after $k$ events).
        2. Define the subject-specific weight:
           $
               hat(eta)_k = (bb(1) {event(k) <= tau, Delta_k in {a, ell}, k < K} hat(nu)_(k) (cal(F)^(-A)_(event(k)), bold(1))) / (hat(S)^c (event(k) | history(k-1))) 
           $
             Then calculate the subject-specific pseudo-outcome
             $
                 hat(R)_k &= (bb(1) {event(k) <= tau, Delta_k = y}) / (hat(S)^c (event(k) | history(k-1))) + hat(eta)_k
             $
                        Regress $hat(R)_k$ on $history(k-1)$ on the data with $event(k-1) < tau$ and $Delta_k in {a, ell}$ to obtain a prediction function $hat(nu)_(k-1) : cal(H)_(k-1) -> RR_+$.
           
            - At baseline, we obtain the estimate $hat(Psi)_n = 1/n sum_(i=1)^n hat(nu)_(0) (L_i (0), 1)$.]
    )
    #colbreak()
    #showybox(
                  title-style: (boxed-style: (:)),
            frame: (
    border-color: blue,
    title-color: blue.lighten(30%),
      footer-color: blue.lighten(80%),
      radius: (top-left: 10pt, bottom-right: 10pt, rest: 0pt)
  ),
        title: [Existing discrete-time ICE estimator],
        [1. For each time point $k = K, K-1, dots, 1$ (starting with $hat(R)_K = Y$):
            Regress $hat(R)_k$ on $(macron(L)_(k-1), macron(A)_(k-1))$ to obtain $hat(nu)_(k-1)$; obtain predictions $hat(R)_(k-1) = hat(nu)_(k-1) (macron(L)_(k-1), bold(1))$.
         2. At baseline, we obtain the estimate $hat(Psi)_n = 1/n sum_(i=1)^n hat(nu)_(0) (L_i (0), 1)$.
         - This approach can be extended to survival outcomes.
        ]
    )
  
        //The main reason for wanting to consider an iterated conditional expectations estimator is its connection with the efficient influence curve @bickel1993efficient, which allows for the construction of (locally) efficient estimators
          //via double/debiased machine learning @chernozhukov2018double or targeted minimum-loss based estimation @laanTargetedMaximumLikelihood2006.    
    ]
    #pop.bibliography-box("ref.bib",style: "apa")
    
])



