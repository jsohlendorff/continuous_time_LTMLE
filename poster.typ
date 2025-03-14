#import "@preview/showybox:2.0.4": showybox
#import "template/definitions.typ": *
#import "@preview/peace-of-posters:0.5.2" as pop
#import "@preview/cetz:0.3.3"

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

#let my_numbering(x) = {
    if (x == 1) {
        return "†"
    } else {
        return "‡"
    }
}

#set footnote(numbering: my_numbering)
#set cite(form: "prose")
#set page("a0", margin: 1.2cm)
#pop.set-poster-layout(pop.layout-a1)
#pop.set-theme(uni-cp)
#set text(size: 25pt)
#let box-spacing = 0.9em
#set columns(gutter: box-spacing)
#set block(spacing: box-spacing)
#pop.update-poster-layout(spacing: box-spacing, body-size: 28pt)

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
    "A new iterated conditional expectations estimator for longitudinal causal effects in continuous time",
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
          iterated conditional expectations (@fig:timegridrytgaard) for estimating causal effects. Recently, @ryalenPotentialOutcomes
          proposed a general identification result for longitudinal causal effects in continuous time.
          We build upon these works and provide a new feasible iterated conditional expectations estimator (@fig:eventgrid) for the estimation of longitudinal causal effects in continuous time.
          #figure(timegrid(new_method:false), caption:  [The figure illustrates the sequential regression approach
              given in @rytgaardContinuoustimeTargetedMinimum2022 for two observations.
          ],) <fig:timegridrytgaard>

        #figure(timegrid(new_method:true), caption: [The figure illustrates the sequential regression approach
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
                An example of a longitudinal dataset from electronic health records or a clinical trial.
                Events are registered at irregular/subject-specific time points.
            ]
        ) <fig:longitudinaldata>
    ]

    #pop.column-box(heading: "Setting")[
        Let $(N^a (t), A (t), N^ell (t), L(t), N^y (t), N^d (t), N^c (t))$#footnote[We associate to this process its natural filtration $cal(F)_t$ implicitly defined on a probability space $(Omega, cal(F), P)$.] be stochastic (jump) processes observed in $[0, tauend]$,
        consisting of a counting process for treatment visits, treatment values, a counting process for treatment covariate measurements, covariate values, and counting processes for the primary event, competing event, and censoring, respectively.
        //Furthermore, $Delta A (t) = 0$ ($Delta L (t) = 0$) if $Delta N^a (t)$ ($Delta N^ell (t) = 0$).
        Furthermore, $A (t) in {0, 1}$ and $L (t) in cal(L)$, where $cal(L) subset.eq RR^d$ is a finite set. 
          
        #assumption[
            In the time interval $[0, tauend]$, there are at most $K - 1 < oo$ many changes of treatment and
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
            history(k) = (event(k), Delta_k, treat(k), covariate(k)) or history(k-1) "and" history(0) = (L(0), A(0)).
        $
        Here $event(k)$ and $Delta_k in {a, ell, y, d, c}$ are the event time and status indicator for the $k$'th event. 
        #assumption[
            For each $k in {1, dots, K}$,  $P(event(k) in dot | history(k-1) = f_(k-1) lt.double m$ #footnote[$m$ is the Lebesgue measure on $RR_+$.], $P(treat(k) in dot | event(k) = t, Delta_k = a, history(k-1) = f_(k-1) lt.double nu_a$, and $P(covariate(k) in dot | event(k) = t, Delta_(k) = ell, history(k-1) = f_(k-1) lt.double nu_ell$.
            //     We assume that the conditional distributions 
            //     $P(event(k) in dot | history(k-1)) lt.double m$ $P$-a.s., and $P(treat(k) in dot | event(k) = t, Delta_k = a, history(k-1)) lt.double nu_a$ $P$-a.s. and $P(covariate(k) in dot | event(k) = t, status(k) = ell, history(k-1)) lt.double nu_ell$ $P$-a.s., where $m$ is the Lebesgue measure on $RR_+$, $nu_a$ is a measure on $cal(A)$, and $nu_ell$ is a measure on $cal(L)$.
            //] <assumptionabscont>
        ]
    ]

    #pop.column-box(heading: "Target parameter")[
        Let $tilde(T)^(bold(1))_k$ and $tilde(Delta)^(bold(1))_k$ be the counterfactual event time and indicator for the $k$'th event had the patient stayed on treatment and initially received treatment (and not been censored).
        Our target parameter $Psi_(tau)^(bold(1)) : cal(M) -> RR$ is the mean interventional absolute risk at time $tau$,
 
        $
            Psi_(tau)^(bold(1)) (P) = mean(P) [sum_(k=1)^K bb(1) {tilde(T)^(bold(1))_k <= tau, tilde(Delta)^(bold(1))_k = y}].
        $
    ]

    #pop.column-box(heading: "Identification")[
        We extend the identification conditions in Theorem 3 of @ryalenPotentialOutcomes. These are stated in our present uncensored setting.
        Let $tilde(Y)_t = (bb(1) {tilde(T)^(bold(1))_1 <= t, tilde(Delta)^(bold(1))_1 = y}, dots, bb(1) {tilde(T)^(bold(1))_K <= t, tilde(Delta)^(bold(1))_K = y})$ and $T^a = inf {t > 0 : A(t) != 1}$.
        For each $k in {1, dots, K}$, we need:
        - *Consistency*:
          $
              bb(1) {tilde(T)^(bold(1))_k <= t, tilde(Delta)^(bold(1))_k = y} bb(1) {T^a > event(k-1), A(0) = 1} = bb(1) {T_k <= t, Delta_k = y} bb(1) {event(k-1) > t, A(0) = 1}
          $
          // Note: >t should be > event(k-1)
          for $t in [0, tauend]$.
        - *Exchangeability*:
          $
              treat(k) perp ((bb(1){tilde(T)^(bold(1))_(k+1) <= t, tilde(D)^(bold(1))_(k+1) = y}, dots, bb(1){tilde(T)^(bold(1))_K <= t, tilde(D)^(bold(1))_K = y}))_(t in [0, tauend]) | Delta_(k) = a, history(k-1)
          $
          // (and
          //$
          //    &lambda^a (t | history(k-1) or (tilde(Y)_t)_(t in [0, tauend]) ) \
          //        &= lim_(h -> 0) (P(t <= event(k) < t+h, Delta_k = a | event(k) >= t, history(k-1), (tilde(Y)_t)_(t in [0, tauend])))/h
          //$
          //does not depend on $(tilde(Y)_t)_(t in [0, tauend])$).
        We hypothesize that the last exchangeability condition may not be necessary.
        - *Positivity*: The weights
          $
              w_k (f_(k-1), t_k) = (bb(1) {a_0 = 1}) / ( pi_0 (l_0)) product_(j=1)^(k-1) ( (bb(1) {a_j = 1})  / ( pi_j ( f_(j-1))))^(bb(1) {delta_j = a}) bb(1) {t_1 < dots < t_k}
          $
          fulfill $mean(P) [w_k (history(k-1), event(k))] = 1$. Here $pi_0 (l_0) = P(A(0) = 1 | L(0) = l_0)$ and $pi_j (f_(j-1)) = P(treat(j) = 1 | Delta_j = a, history(j-1) = f_(j-1))$.
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
              Under the assumptions of *consistency*, *exchangeability*, and *positivity*, the target parameter is identified via
              $
                  Psi_(tau)^(bold(1)) (P) = mean(P) [sum_(k=1)^K w_k (history(k-1), event(k)) bb(1) {T_k <= tau, Delta_k = y}].
              $
          ]
        
    ]
    
    #pop.column-box(heading: "Iterated conditional expectation estimator")[
        //Moreover, the estimator is more stable than inverse probability weighted estimators.
        Let $S^c (t | history(k))$ be the conditional survival function of the censoring time given the history of the $k$ previous events
        and $cal(F)^(-A)_(event(k))$ denote the history without the treatment process.
      
        #showybox(
            title-style: (boxed-style: (:)),
            frame: (
                border-color: blue,
                title-color: blue.lighten(30%),
                footer-color: blue.lighten(80%),
                radius: (top-left: 10pt, bottom-right: 10pt, rest: 0pt)
            ),
            title: "Proposed continuous-time ICE algorithm",
            [- For each event point $k = K, K-1, dots, 1$ (starting with $k = K$):
                1. Obtain $hat(S)^c (t | history(k-1))$ by fitting a cause-specific hazard model for the censoring via the interevent time $S_((k)) = event(k) - event(k-1)$,
                   regressing on $history(k-1)$ (among the people who are still at risk after $k-1$ events).
                2. Define the subject-specific weight:
                   $
                       hat(eta)_k = (bb(1) {event(k) <= tau, Delta_k in {a, ell}} hat(nu)_(k) (cal(F)^(-A)_(event(k)), bold(1))) / (hat(S)^c (event(k) | cal(F)^(-A)_(event(k-1)), bold(1))) bb(1) {k < K}
                   $
                   Then calculate the subject-specific pseudo-outcome
                   $
                       hat(R)_k &= (bb(1) {event(k) <= tau, Delta_k = y}) / (hat(S)^c (event(k) | cal(F)^(-A)_(event(k-1)), bold(1))) + hat(eta)_k
                   $
                   If $k > 1$: Regress $hat(R)_k$ on $cal(F)_(event(k-1))$ on the data with $event(k-1) < tau$ and $Delta_k in {a, ell} $ to obtain a prediction function $hat(nu)_(k-1) : cal(H)_(k-1) -> RR_+$.
                   
                   If $k = 1$: Regress $hat(R)_k$ on $L(0), A(0)$ to obtain a prediction function $hat(nu)_(0) : cal(H)_(0) -> RR_+$.
           
             - At baseline, we obtain the estimate $hat(Psi)_n = 1/n sum_(i=1)^n hat(nu)_(0) (L_i (0), 1)$.] 
        )
        #colbreak()
    ]
    #pop.column-box(heading: "Future directions/challenges")[
        - Implementation of the method and application on real data.
        - Debiasing via the efficient influence function (@chernozhukovDoubleMachineLearning2018).
        - Few individuals may have a high number of events, leading to potentially small sample sizes in the iterated regressions.
          //*Proposed solution*: Use data-adaptive (in the sense of distinguishing sample sizes) rule for model selection.
    ]
    
    #pop.bibliography-box("ref.bib",style: "apa")
])


