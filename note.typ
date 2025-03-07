#import "@preview/fletcher:0.5.5": node, edge, diagram
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/cetz:0.3.2"
#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm
#set cite(form: "prose")
#show ref: it => [#text(fill: blue)[#it]]
#show: arkheion.with(
    title: "A Novel Approach to the Estimation of Causal Effects of Multiple Event Point Interventions in Continuous Time",
    authors: (
        (name: "Johan Sebastian Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen"),
    ),
    abstract: [In medical research, causal effects of treatments that may change over
            time on an outcome can be defined in the context of an emulated target
            trial. We are concerned with estimands that are defined as contrasts of
            the absolute risk that an outcome event occurs before a given time
            horizon $tau$ under prespecified treatment regimens. Most of the
            existing estimators based on observational data require a projection
            onto a discretized time scale @Rose2011. We consider a recently developed continuous-time approach to
            causal inference in this setting @rytgaardContinuoustimeTargetedMinimum2022, 
            which theoretically allows preservation of the precise event timing on a
            subject level. Working on a continuous-time scale may improve the
            predictive accuracy and reduce the loss of information. However,
            continuous-time extensions of the standard estimators comes at the cost
            of increased computational burden. We will discuss a new
            sequential regression type estimator for the continuous-time framework
            which estimates the nuisance parameter models by backtracking through
            the number of events. This estimator significantly reduces the
            computational complexity and allows for efficient, single-step targeting
            using machine learning methods from survival analysis and point
            processes, enabling robust continuous-time causal effect estimation.
    ]
)

#set page(margin: (left: 10mm, right: 10mm, top: 25mm, bottom: 30mm))
#show math.equation: set text(9pt)
#show: thmrules.with(qed-symbol: $square$)

// typst-ts-watch

= Introduction
In medical research, the estimation of causal effects of treatments over time is often of interest.
We consider a longitudinal continuous-time setting that is very similar to @rytgaardContinuoustimeTargetedMinimum2022
in which patient characteristics can change at subject-specific times. 
This is the typical setting of registry data, which usually
contains precise information about when events occur, e.g.,
information about drug purchase history, hospital visits, and laboratory measurements.
This approach offers an advantage over discretized methods, as it eliminates the need to select a time grid mesh for discretization,
which can affect both the bias and variance of the resulting estimator.
A continuous-time approach would adapt to the events in the data. 
Furthermore, continuous-time data captures more precise information about when events occur, which may be valuable in a predictive sense.
Let $tauend$ be the end of the observation period.
We will focus on the estimation of the interventional cumulative incidence function in the presence of time-varying confounding at a specified time horizon $tau < tauend$.

#assumption("Bounded number of events")[
In the time interval $[0, tauend]$ there are at most $K - 1 < oo$ many changes of treatment and
        covariates in total for a single individual.
        Without loss of register data applications, we assume that the
        maximum number of treatment and covariate changes of an individual
    is bounded by $K = 10,000$. Practically, we shall adapt $K$ to our data and our target parameter.
    We let $K-1$ be given by the maximum number of non-terminal events for any individual in the data.
] <assumptionbounded>

#assumption("No simultaneous jumps")[
    The counting processes $N^a$, $N^ell$, $N^y$, $N^d$, and $N^c$ have with probability 1 no jump times in common. 
] <assumptionnosimultaneous>

Let $kappa_i (tau)$ be the number of events for individual $i$ up to time $tau$.
In @rytgaardContinuoustimeTargetedMinimum2022, the authors propose a continuous-time LTMLE for the estimation of causal effects in which a single step of the targeting procedure must update each of the nuisance estimators $sum_(i = 1)^n kappa_i (tau)$ times. We propose an estimator where the number of nuisance parameters is reduced to $tilde max_i kappa_i (tau)$ in total,
and, in principle, only one step of the targeting procedure is needed to update all nuisance parameters.
We provide an iterative conditional expectation formula that, like @rytgaardContinuoustimeTargetedMinimum2022,
iteratively updates the nuisance parameters. The key difference is that the estimation of the nuisance parameters can be performed
by going back in the number of events instead of going back in time.
The different approaches are illustrated in @fig:timegridrytgaard and @fig:eventgrid
for an outcome $Y$ of interest. 
Moreover, we argue that the nuisance components can be estimated with existing machine learning algorithms
from the survival analysis and point process literature.
As always let $(Omega, cal(F), P)$ be a probability space on which all processes
and random variables are defined.

#figure(cetz.canvas(length: 1.8cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 2),
    stroke: (thickness: 0.4pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .22,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 1pt)
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
      content("lend.start", [#text(size: 6pt)[$tau_"end"$]],anchor: "north")

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
        
        content(v.name + ".start", [#text(size: 6pt)[#v.mformat]], anchor: anchor)
      }
  }
    for v in (2,4) {
        line((v, 0.75), (v, 1.25), stroke: red)
    }
    // Deal with the marks/events
    
    let grid2 = (1,1.7, 2.4,2.8)
    
    group({time_grid((0,1),(5,1), grid2, anchor: "north-east")})
    set-style(mark: (end: ">", scale: 0.5))
    bezier((1,1.25), (2,1.25),(1.5,2.4), stroke: blue)
    bezier((1.7,0.75), (2,0.75), (1.85,0.25), stroke: blue)
    bezier((2.4,1.25), (4,1.25), (3,2), stroke: blue)
        bezier((2.8,0.75), (4,0.75), (3.4,0.25), stroke: blue)
}), caption:  [The "usual" approach where time is discretized. Each event time and its corresponding mark
    is rolled forward to the next time grid point, that is the values of the observations are updated based on the
    on the events occuring in the previous time interval.
]) <fig:discretetimegrid>

#figure(cetz.canvas(length: 0.9cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 2),
    stroke: (thickness: 0.4pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .22,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 1pt)
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
      content("lend.start", [#text(size: 6pt)[$tau_"end"$]],anchor: "north")

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
        line((v.value, -1.5+start_y), (v.value, 1.5+start_y), stroke: red,name: v.name)
        content(v.name + "." + where, [#text(size: 6pt)[#v.mformat]], anchor: anchor)
      }
    }

    rect((0,1.5), (2.8,-1.5),fill:gray,stroke:none)
    let grid1 = (2.5,4.4,6.4)
    // Deal with the marks/events
    eventfun(grid1)
    
    let grid2 = (1,1.7, 2.3,2.8)
    eventfun(grid2, where: "end", anchor: "south")
    
    group({time_grid((0,-1),(10,-1), grid1,inc: 0.1,anchor: "south")})
    group({time_grid((0,1),(10,1), grid2)})
}), caption:  [The figure illustrates the sequential regression approach
    given in @rytgaardContinuoustimeTargetedMinimum2022 for two observations:
    Let $t_1 < dots < t_m$ be all the event times in the sample.
    Then, given $mean(Q)[Y | cal(F)_(t_(r))]$,
    we regress back to $mean(Q)[Y | cal(F)_(t_(r-1))]$ (through multiple regressions).
],) <fig:timegridrytgaard>

#figure(cetz.canvas(length: 0.9cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 2),
    stroke: (thickness: 0.4pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .22,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 1pt)
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
      content("lend.start", [#text(size: 6pt)[$tau_"end"$]],anchor: "north")

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
        
        content(v.name + ".start", [#text(size: 6pt)[#v.mformat]], anchor: anchor)
      }
    }

    rect((0,1.5), (1.7,0.5),fill:gray,stroke:none)
    rect((0,-1.5), (4.4,-0.5),fill:gray,stroke:none)
    let grid1 = (2.5,4.4,6.4)
    // Deal with the marks/events
    
    let grid2 = (1,1.7, 2.3,2.8)
    
    group({time_grid((0,-1),(10,-1), grid1, anchor: "north-east")})
    group({time_grid((0,1),(10,1), grid2, anchor: "north-east")})
}), caption: [The figure illustrates the sequential regression approach
    proposed in this article. For each event $k$ in the sample, we regress back on the history $history(k-1)$.
    That is, given $mean(Q)[Y | history(k)]$,
    we regress back to $mean(Q)[Y | history(k-1)]$.
    In the figure, $k=3$.
],) <fig:eventgrid>

// Let $cumhazard(k, x, t)$ be the cumulative hazard of $x$ of the $(k+1)$'th event at time $t$ given the history up to the $k$'th event.
// We focus on estimating $cumhazard(k, x, t)$ for $k = 0, dots, K$ for $K >= 0$ rather than $Lambda^x (t \| cal(F)_(t -))$.
// Here $cal(F)_(T_k)$ is the information up to the $k$'th event -- a so-called stopping time $sigma$-algebra.
//Each of these $sigma$-algebras can be represented by a fixed number of random variables, so that regression can be applied at each event point. 
//We let $pi_0(dot | covariate(0))$ be the density of the baseline treatment given the covariates at time 0
//(with respect to some measure $nu_a$) and
//$mu_0$ be the density of time-varying covariates at time 0 (with respect to some measure $nu_ell$).

= Setting and Notation
First, we assume that at baseline,
we observe the treatment $treat(0)$ and the time-varying confounders
at time 0, $covariate(0)$. The time-varying confounders can in principle include covariates
which do not change over time, but for simplicity of notation, we will include them among
those that do change over time. Also, we assume that we have two treatment options, $A(t) = 0, 1$ (e.g., placebo and active treatment).
The time-varying confounders and treatment are assumed to take values in $RR^m$ and $RR$,
and that $L(t) : Omega -> RR^m$ and $A(t) : Omega -> RR$ are measurable for each $t >= 0$, respectively.
These processes are assumed to be càdlàg, i.e., right-continuous with left limits.
Furthermore, the times at which the treatment and covariates may only change at the jump times
of the counting processes $N^a$ and $N^ell$, respectively which makes $L(t)$ and $A(t)$ into jump processes (@last1995marked). The jump times of these counting processes
thus represent visitation times. 

We are interested in the cumulative incidence function, so we also observe 
$N^y$ and $N^d$ corresponding to the counting processes for the primary and competing event, respectively.
Finally, let $N^c$ be the counting process for the censoring counting process.
Our the outcome of interest is $Y_tau = I(T <= tau, Delta = y)$, where $T$ is the time of the terminal event and $Delta in {y, d}$ is the indicator for which terminal event occurred.
We assume that the jump times differ with probability 1 (@assumptionnosimultaneous).
Moreover, we assume that only a bounded number of events occur for each individual in the time interval $[0, tauend]$ (@assumptionbounded).

We consider the framework in @rytgaardContinuoustimeTargetedMinimum2022 and
cast it into the framework of marked point processes. To this end, we can define the jump process $M$ as
$
    M (s) = (N^y (s), N^d (s), N^c (s), L(s), N^ell (s), A(s), N^a (s))
$
and consider its corresponding natural filtration by 
$
    cal(F)^M_t = sigma(N^y (s), N^d (s), N^c (s), L(s), N^ell (s), A(s), N^a (s) | s <= t)
$
and the corresponding point process given by
$
    (pi_n (M), k_n (M))
$
where $pi_n (M) = event(n)$ is the $n$'th jump time of $M$ and
$
    k_n (M) = cases((N^y (event(n)), N^d (event(n)), N^c (event(n)), L(event(n)), N^ell (event(n)), A(event(n)), N^a (event(n))) "if" event(n) < oo \ nabla "otherwise")
$
Consider the counting process $N$ of $M$ given by
$
    N (d t, d x) = sum_(n = 1)^(K) delta_((pi_n (M), k_N (M))) (d t, d x) 
$
By reparametrization and @assumptionnosimultaneous, we can essentially use the random measure
$
    tilde(N) (d t, d x)   = sum_(n = 1)^(K) delta_(pi_n (M)) (d t) delta_((D_n, covariate(n), treat(n))) (d x)
$
instead, since their histories are the same $(cal(F)_t = sigma(N ((0, s], dot) | s <= t) or cal(F)_0=tilde(cal(F))_t = sigma(tilde(N) ((0, s], dot) | s <= t)) or cal(F)_0$.
Moreover its natural filtration (Theorem 2.5.10 of @last1995marked under so-called _minimality_ which we will just assume) satisfies, 
$
    cal(F)^N_t = sigma(tilde(N) ((0, s], dot) | s <= t) or cal(F)_0= cal(F)^M_t
$
for $cal(F)_0 = sigma(covariate(0), treat(0))$.
Since $N$ is a marked point process, we may assume the filtration to be right-continuous. Then $history(k) = (event(k), status(k), L_((k)), A_((k))) or history(k-1)$ is the history up to the $k$'th event.
Our observations can thus be assumed to be on the form $O=history(K)$.

#assumption("Conditional distributions of jumps and marks")[
    We assume that the conditional distributions $P(event(k) in dot | history(k-1)) lt.double m$ $P$-a.s., and $P(treat(k) in dot | event(k) = t, status(k) = a, history(k-1)) lt.double nu_a$ $P$-a.s. and $P(covariate(k) in dot | event(k) = t, status(k) = ell, history(k-1)) lt.double nu_ell$ $P$-a.s., where $m$ is the Lebesgue measure on $RR_+$, $nu_a$ is a measure on $cal(A)$, and $nu_ell$ is a measure on $cal(L)$.
        ] <assumptionabscont>

#theorem("Existence of compensator")[
    Let $bb(F)_k = (RR_+ times {a, ell, c, d, y} times cal(A) times cal(L))^k$.
    Under @assumptionbounded, @assumptionnosimultaneous, and @assumptionabscont,
    there exists functions for $k=1, dots, K$, functions $lambda_k^x  (dot, dot): RR_+ times bb(F)_k -> RR_+$, $pi_k (dot, dot, dot): RR_+ times cal(A) times bb(F)_k -> RR_+$, and $mu_k (dot, dot, dot): RR_+ times cal(L) times bb(F)_k -> RR_+$ such that
   $
    Lambda(d t, d m, d a, d l) &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} delta_(a) (d m) hazard(a, t, k-1) densitytrt(t, d a, k-1)  \
        &+ bb(1) {event(k-1) < t <= event(k)} delta_(ell) (d m) hazard(ell, t, k-1) densitycov(t, d l, k-1)  \
        &+ bb(1) {event(k-1) < t <= event(k)} delta_(y) (d m) hazard(y, t, k-1)  \
        &+ bb(1) {event(k-1) < t <= event(k)} delta_(d) (d m) hazard(d, t, k-1)  \
        &+ bb(1) {event(k-1) < t <= event(k)} delta_(c) (d m) hazard(c, t, k-1)  
   $
    is a $P$-$cal(F)_t$-compensator measure of $N$. As a consequence we have,
    #math.equation(block: true, numbering: "(1)")[
        $
            &P(event(k) <= s, status(k) = x, covariate(k) in d l, treat(k) in d a | history(k-1)) \
                &= integral_0^s underbrace(exp(-sum_(x=y, d, ell, a, c) integral_(0)^(t) hazard(x, s, k-1) upright(d) s), "probability of surviving up to" t.) underbrace(hazard(x, t, k), "probability that it was an event of type "x) \
                &( underbrace(integral_(bb(L)) densitycov(t, x, k-1) nu_ell (upright(d) x), "probability of" covariate(k) in bb(L) "given " status(k) = ell "and" event(k) = t) delta_((ell, treat(k-1))) ({x}, d a) + \
                    &+underbrace(integral_(bb(A)) densitytrt(t, x, k-1) nu_a (upright(d) x), "probability of" treat(k) in bb(A) "given " status(k) = a "and" event(k) = t) delta_((a, covariate(k-1))) ({x}, d l) + delta_(({x}, emptyset, emptyset)) ({d,y,c}, d l, d a)) upright(d) t.
        $] <jointdensity>
    on the event $event(k-1) < s$.
] <thm:jointdensity>
#proof[
    Simply use Theorem 4.1.11 of @last1995marked which states that
    $
        Lambda(d t, d m, d a, d l) &= sum_(k: event(k-1) < oo) bb(1) {event(k-1) < t <= event(k)} P( (event(k), status(k), covariate(k), treat(k)) in (d t, d m, d a, d l) | history(k-1)) / P(event(k) >= t | history(k-1)) \ 
    $
    is a $P$-$cal(F)_t$-compensator measure of $N$. Now rewrite $P( (event(k), status(k), covariate(k), treat(k)) in (d t, d m, d a, d l) | history(k-1)) = P( (status(k), covariate(k), treat(k)) in (d m, d a, d l) | event(k) = t, history(k-1)) P(event(k) = d t | history(k-1))$.
    Under @assumptionabscont, we can write
    $
        P(status(k) = x | event(k) = t, history(K-1)) P(event(k) in d t | history(k-1)) / P(event(k) >= t | history(k-1)) = hazard(x, t, k-1) d t
    $
    which is simply the cause-specific hazard function of the $k$'th event.
    Also, we can define
    $
        densitytrt(t, d a, k-1)  &=  P( ( covariate(k), treat(k)) in ( {L_((k-1))}, d a) | event(k) = t, status(k) = a, history(k-1)) \
            &= P(treat(k) in d a | event(k) = t, status(k) = a, history(k-1)) \ \
            densitycov(t, d l, k-1)  &= P( ( covariate(k), treat(k)) in ( d l, {A_((k-1))}) | event(k) = t, status(k) = ell, history(k-1)) \
            &= P(covariate(k) in d l | event(k) = t, status(k) = ell, history(k-1))
    $
    and the result follows. The latter conclusion can be seen by Theorem 4.3.8 of @last1995marked.
]

// == Example for $K=2$ with $cal(L) = {0, 1}$ and $cal(A) = {0,1}$
// We represent the marked point process via a simple diagram given in @fig:multi-state.
// We consider the set of states represented by time 0,
// first treatment visit ($a$) set to 1, first treatment visit ($a$) set to 0, first covariate visit ($ell$) set to 1, first covariate visit ($ell$) set to 0, primary event, and competing event.

// The previous theorem gives the transition intensities 
// If we represent the first state as time 0 and second state as the first treatment visit ($a$) set to 1.
// Then the counting process,
// $
//     N_12 (t) = I(event(1) <= t, status(1) = a, treat(1) = 1, covariate(1) = covariate(0))
// $
// has the intensity by mg given by
// $
//     hazard(a, t, 0) densitytrt(t, 1, 0)
// $
// with similar expressions for transitions to the other states.
// Moreover, the probability of making this transition before time $t$ is given by @jointdensity.

// #figure(diagram(spacing: (12mm, 7.5mm), debug: false, node-stroke: 0.35pt, node-inset: 10.5pt, label-size: 7pt, {
//     let (novisit, treat_visit, treat_visit_2, cov_visit, cov_visit_2, death, comp_risk) = ((0,0), (1.3,-1.3), (1.3,1.3), (-1.3,-1.3), (-1.3,1.3), (0, 2.6), (0, -2.6))
//     node(novisit, [#text([No patient visit \ $history(0) = (covariate(0), treat(0))$], size: 8pt)])
//     node(treat_visit, [#text([1st patient visit ($a$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), covariate(0), 1)$) ], size: 8pt)], fill: gray)
//     node(treat_visit_2, [#text([1st patient visit ($a$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), covariate(0), 0))$) ], size: 8pt)], fill: gray)
//     node(cov_visit, [#text([1st patient visit ($ell$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), 1, treat(0))$)], size: 8pt)], fill: gray)
//     node(cov_visit_2, [#text([1st patient visit ($ell$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), 0, treat(0))$)], size: 8pt)], fill: gray)
//     node(death, [#text([Primary event], size: 8pt)])
//     node(comp_risk, [#text([Competing event], size: 8pt)])

//     edgemsm(novisit, treat_visit, [$hazard(a, t, 0) densitytrt(t, 1, 0)$])
//     edgemsm(novisit, cov_visit, [$hazard(ell, t, 0)  densitycov(t, 1, 0)$], label-pos:0.4)
//     edgemsm(novisit, treat_visit_2, [$hazard(a, t, 0) densitytrt(t, 0, 0)$])
//     edgemsm(novisit, cov_visit_2, [$hazard(ell, t, 0)  densitycov(t, 0, 0)$])
    
//     edgemsm(novisit, death, [$hazard(y, t, 0)$])
//     edgemsm(novisit, comp_risk, [$hazard(d, t, 0)$])
//     //edgemsmcens(novisit, censoring, [$hazard(c, t, 0)$])

//     //edgemsm(treat_visit, treat_visit_2, [$hazard(a, t, 1)$]) 
//     //edgemsm(treat_visit, cov_visit_2, [$hazard(ell, t, 1)$], label-pos: 0.8)
//     edgemsm(treat_visit, death, [$hazard(y, t, 1)$], label-pos: 0.75)
//     edgemsm(treat_visit, comp_risk, [$hazard(d, t, 1)$])
//     edgemsm(treat_visit_2, death, [$hazard(y, t, 1)$])
//     edgemsm(treat_visit_2, comp_risk, [$hazard(d, t, 1)$], label-pos: 0.75)
//     //edgemsmcens(treat_visit, censoring, [$hazard(c, t, 1)$])

//     edgemsm(cov_visit, death, [$hazard(y, t, 1)$], label-pos: 0.75)
//     edgemsm(cov_visit, comp_risk, [$hazard(d, t, 1)$])
//     edgemsm(cov_visit_2, death, [$hazard(y, t, 1)$])
//     edgemsm(cov_visit_2, comp_risk, [$hazard(d, t, 1)$], label-pos: 0.75)
// }), caption: [A multi-state model for $K=2$ with $cal(L) = cal(A) = {0, 1}$.])
// <fig:multi-state>

= A pragmatic approach to continuous-time causal inference
One classical causal inference perspective requires that we know how the data was generated up to unknown parameters (NPSEM) #citep(<pearlCausalityModelsReasoning2009>).
This approach has only to a small degree been discussed in continous-time causal inference literature (@roeysland2024).
This is initially considered in the uncensored case, but is later extended to the censored case.
For a moment, we ponder how the data was generated given a DAG. The DAG given in the section provides
a useful tool for simulating continuous-time data, but not for drawing causal inference conclusions. 
For the event times, we can draw a figure representing the data generating mechanism which is shown in @fig:dag.
Some, such as @chamapiwa2018application, write down this DAG, but with an arrow from $event(k)$ to $covariate(k)$ and $treat(k)$
instead of displaying a multivariate random variable which they deem the "time-as-confounder" approach
to allow for irregularly measured data (see @fig:simulationdag).
Fundamentally, this arrow would only be meaningful if the event time was known prior to the treatment and covariate value measurements,
which they might not be. This can make sense if the event is scheduled ahead of time, but for, say, a stroke
the time is not measured prior to the event. Because a cause must precede an effect,
this makes the arrow invalid from a philosophical standpoint.
On the other hand, DAGs such as the one in @fig:dag, are not informative about the causal relationships
between the variables are. This issue with simultaneous events is likely what has led to the introduction of local independence graphs (@localindependence)
but is also related to the notion that the treatment times are not predictable (that is knowable just prior to the event) as in @ryalenPotentialOutcomes.

#figure(
    diagram(node-stroke: 0.7pt, node-shape: circle, {
        let (historyprior, inst, historyfuture) = ((1,0), (2.5,0), (4,0))
        let (l0, a0, f1) = ((6, 0), (7, -0.5), (7, 0.5))
        // Define the nodes (variables)
        node(enclose: ((0,-1.5), (4.5,1.5)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k > 0$:])
        node(enclose: ((5.5,-1), (8,1)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k = 0$:])
        dagnode(historyprior, [$historypast(k - 1)$])
        node(inst, [#text(size:6pt)[$(event(k), status(k), covariate(k), treat(k))$]])
        dagnode(historyfuture, [$historynext(k + 1)$])

        edgemsmcens(historyprior, inst)
        edgemsmcens(inst, historyfuture)
    
        dagnode(l0, [$covariate(0)$])
        dagnode(a0, [$treat(0)$])
        dagnode(f1, [$historynext(1)$])

        edgemsm(l0, a0)
        edgemsmcens(a0, f1)
        edgemsmcens(l0, f1)        
    }),
    caption: [
        A DAG representing the relationships between the variables of $O$.
        The dashed lines indicate multiple edges from the dependencies in the past and into the future.
        Here $historypast(k)$ is the history up to and including the $k$'th event and $historynext(k)$ is the history after and including the $k$'th event.
    ],
) <fig:dag>

#figure(
    diagram(node-stroke: 0.7pt, node-shape: circle, {
        let (historyprior, timestatus, treatment, covar, historyfuture) = ((1,0), (2.5,0), (3,-1), (3,1), (4,0))
        let (l0, a0, f1) = ((6, 0), (7, -0.5), (7, 0.5))
        // Define the nodes (variables)
        node(enclose: ((0,-1.5), (4.5,1.5)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k > 0$:])
        node(enclose: ((5.5,-1), (8,1)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k = 0$:])
        dagnode(historyprior, [$historypast(k - 1)$])
        dagnode(timestatus, [#text(size:7pt)[$(event(k), status(k))$]])
        dagnode(covar, [$covariate(k)$])
        dagnode(treatment, [$treat(k)$])
        dagnode(historyfuture, [$historynext(k + 1)$])
        

        edgemsmcens(historyprior, treatment)
        edgemsmcens(historyprior, covar)
        edgemsmcens(historyprior, timestatus)
        edgemsm(timestatus, covar)
        edgemsm(timestatus, treatment)
        edgemsmcens(treatment, historyfuture)
        edgemsmcens(covar, historyfuture)
        edgemsmcens(timestatus, historyfuture)
        
    
        dagnode(l0, [$covariate(0)$])
        dagnode(a0, [$treat(0)$])
        dagnode(f1, [$historynext(1)$])

        edgemsm(l0, a0)
        edgemsmcens(a0, f1)
        edgemsmcens(l0, f1)        
    }),
    caption: [
        A DAG for simulating the data generating mechanism or such as those that may be found in @chamapiwa2018application.
        The dashed lines indicate multiple edges from the dependencies in the past and into the future.
        Here $historypast(k)$ is the history up to and including the $k$'th event and $historynext(k)$ is the history after and including the $k$'th event.
    ],
) <fig:simulationdag>


We now take an interventionalist stance to causal inference such as the one given in @ryalenPotentialOutcomes.
In the interventionalist school of thought, one tries to emulate a randomized controlled trial.
In the continuous-time longitudinal setting, this can e.g., correspond to a trial in which there is perfect compliance.
We reformulate the conditions of @ryalenPotentialOutcomes to our setting, stating the conditions directly
in terms of the events instead of using martingales. For simplicity, we presuppose that there are two treatment levels (0/1).
As in randomized trials, we suppose that there is a treatment plan $g_k$ at each event point
which specifies the treatment that the person observation should have at teach event point
which is a treatment event point that is $g_k : RR_+ times bb(F)_(k-1) -> {0, 1}$.
Specifically, the plan specifies that $treat(k) = g_k (event(k), history(k-1))$ if $event(k) < oo$ and $status(k) = a$.

We assume the existence of potential outcome process
$
    tilde(O)^g &= (covariate(0), tilde(A) (0), tilde(T)_((1)), tilde(D)_((1)), tilde(A)(tilde(T)_((1))), tilde(L)(tilde(T)_((1))), dots, tilde(T)_((K)), tilde(D)_((K))) \
        &"with" tilde(A) (tilde(T)_((k))) = cases(g_k (tilde(T)_((k)), history(k-1)) "if" tilde(T)_k < oo "and" status(k) = a, tilde( A ) (tilde(T)_((k-1))) "if" tilde(T)_k < oo "and" status(k) != a, nabla "otherwise")
$
We choose not to index the random variables with $g$ when it can clearly be inferred from the context.
Our potential outcome, which is part of this process, is given by
$
    tilde(Y)^g_t = (bb(1){tilde(T)_1 <= t, tilde(D)_1 = y}, dots, bb(1){tilde(T)_K <= t, tilde(D)_K = y})
$ 

We are then interested in estimating the causal parameter given in @def:targetparameter.

#definition("Target parameter")[
    Our target parameter $Psi_(tau)^g : cal(M) -> RR$ is the mean interventional potential outcome at time $tau$ given the intervention plan $g$,
    $
        Psi_(tau)^g (P) = mean(P) [sum_(k=1)^K bb(1) {tilde(T)_k <= tau, tilde(D)_k = y}]
    $
] <def:targetparameter>

The three identifying conditions for the target parameter are as follows:

1. For all $k=1,dots,K$, $bb(1) {tilde(T)_k <= tau, tilde(D)_k = y} = bb(1) {T_k <= tau, D_k = y}$ $P$-a.s. if there does not exist a treatment plan $j < k$ such that $treat(j) != g_j (event(j), history(j-1))$ with $status(j) = a$ and $event(j) < oo$ and $treat(0) = g_0 (covariate(0))$ (consistency).
2. For all $k=1,dots,K$, $treat(k) perp (bb(1){tilde(T)_(k+1) <= t, tilde(D)_(k+1) = y}, dots, bb(1){tilde(T)_K <= t, tilde(D)_K = y}) | status(k) = a, history(k-1)$  (exchangeability).
3. Let $w_(k-1) (l_0, a_0, f_1, dots, f_k) = (bb(1) {a_0 = g(l_0)}) / (pi_0 (g(l_0)) ) product_(j=1)^(k-1) ( (bb(1) {a_j = g_j (t_j, f_(j-1))})  / (pi_j (t_j, g_j (t_j, f_(j-1)))) )^(bb(1) {d_j = a}) bb(1) {t_1 < dots < t_k}$.
   The measure $Q_tau = (sum_(k=1)^K w_k) dot P$ is a valid probability measure (positivity).

Then we have the following theorem
#theorem("Identification via inverse probability weights")[
    Under the conditions of 1., 2., and 3., the target parameter is identified by
        $
            Psi_(tau)^g (P) = mean(P) [sum_(k=1)^K w_(k-1) bb(1) {T_k <= tau, D_k = y}]
        $
]
#proof[
    We will show this by proving that $psi_(k,tau) (P) = mean(P) [w_(k-1) bb(1) {T_k <= tau, D_k = y}] = mean(P) [bb(1) {tilde(T)_k <= tau, tilde(D)_k = y}]$.
    Let $Y_(k,j)^* = mean(P) [ bb(1) {tilde(T)_k <= tau, tilde(D)_k = y} | (event(j-1), status(j-1), covariate(j-1), cal(F)^(-a)_(event(j-2)))]$ \
    Let $g_k^* = g_k$ if $status(k) = a$ and $event(k) < oo$ and $g_k^* = g_(k-1)^*$ otherwise.
    We use the law of iterated expectations to find that
    $
        psi_(k,tau) (P) &= mean(P) [w_(k-1) mean(P) [ bb(1) {T_k <= tau, D_k = y} | history(k-1)]] \
            &= mean(P) [w_(k-1) bb(1) {t_1 < dots < t_(k-1)} mean(P) [ bb(1) {T_k <= tau, D_k = y} | (event(k-1), status(k-1), covariate(k-1), treat(k-1) = g_k^* (event(k-1), cal(F)_(event(k-2))), dots, treat(0) = g_0 (covariate(0)), covariate(0))]] \
            &= mean(P) [w_(k-1) bb(1) {t_1 < dots < t_(k-1)} mean(P) [ bb(1) {tilde(T)_k <= tau, tilde(D)_k = y} | (event(k-1), status(k-1), covariate(k-1), treat(k-1) = g_k^* (event(k-1), cal(F)_(event(k-2))), dots, treat(0) = g_0 (covariate(0)), covariate(0))]] \
            &= mean(P) [w_(k-1) bb(1) {t_1 < dots < t_(k-1)} mean(P) [ bb(1) {tilde(T)_k <= tau, tilde(D)_k = y} | (event(k-1), status(k-1), covariate(k-1), cal(F)^(-a)_(event(k-2)))] \
                &= mean(P) [w_(k-2) bb(1) {t_1 < dots < t_(k-1)} Y_k^* mean(P) [((bb(1) {treat(k-1) = g_(k-1) (event(k-1), cal(F)^g_(event(k-1)))}) / (pi_(k-1) (event(k-1), g_(k-1) (event(k-1), cal(F)_(event(k-1)))) ))^(bb(1) {status(k-1) = a})   | (event(k-1), status(k-1), covariate(k-1), cal(F)^(-a)_(event(k-2))) ] \
                    &= mean(P) [w_(k-2) bb(1) {t_1 < dots < t_(k-1)} Y_k^*] \
                    &= mean(P) [w_(k-2) bb(1) {event(1) < dots < event(k-2)} mean(P) [Y_k^* bb(1){event(k-2) < event(k-1)} | cal(F)^(-a)_((event(k-2))) ] \
                        &= mean(P) [w_(k-2) bb(1) {event(1) < dots < event(k-2)} Y_(k,k-1)^* ] \
                        & dots \
                        &= mean(P) [bb(1) { tilde(T)_k <= tau, tilde(D)_k = y}]
    $
]

//Also note that according to our example with multi-state models with $cal(A)= cal(L) = {0,1}$: If $T$ is the time to
//the first transition into the primary event or competing event state and 𝐷 corresponds to the terminal event type,
//then our target parameter does indeed correspond to the cumulative incidence function at
//time $tau$ with $T$ and $D$ being the time-to-event and the status, respectively. The target parameter simply
//summarizes that this can either happen as the first or second event.

We first state and prove a formula for at target parameter that is not causal, but we will use it to identify the causal parameter.
This will be useful for the derivation of the efficient influence function. 

// should just be identification not of conditional densities
#lemma[
    Let $macron(Q)_K = I(event(K) <= tau, status(K) = y)$ and
    $macron(Q)_k = mean(P) [sum_(j=k+1)^K I(event(j) <= tau, status(j) = y) | history(k)]$.
    Then,
    $
        macron(Q)_(k-1) &= mean(P) [I(event(k) <= tau, status(k) = ell) macron(Q)_(k)(treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
            &+ I(event(k) <= tau, status(k) = a) mean(P) [macron(Q)_(k)(treat(k), covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k), history(k-1)] \
            & + I(event(k) <= tau, status(k) = y) mid(|) history(k-1)]
    $
    for $k = K, dots, 1$.
    Thus, $mean(P) [sum_(k=1)^K I(event(k) <= tau, status(k) = y)]= mean(P) [macron(Q)_0]$.
]<thm:parameter>

#proof[
    We find
    $
        macron(Q)_k &= mean(P) [sum_(j=k+1)^K I(event(j) <= tau, status(j) = y) | history(k)] \
            &= mean(P) [mean(P) [mean(P) [sum_(j=k+1)^K I(event(j) <= tau, status(j) = y)  | history(k+1)]  | event(k+1), status(k+1), history(k) ] | history(k)] \
            &= mean(P) [I(event(k+1) <= tau, status(k+1) = y) \
                &#h(2cm)+ mean(P) [mean(P) [sum_(j=k+2)^K I(event(j) <= tau, status(j) = y) | history(k+1)]  | event(k+1), status(k+1), history(k)]
                mid(|) history(k)] \
            &= mean(P) [I(event(k+1) <= tau, status(k+1) = y) \
                &+ I(event(k+1) <= tau, status(k+1) = a) mean(P) [mean(P) [sum_(j=k+2)^K I(event(j) <= tau, status(j) = y) | history(k+1)]  | event(k+1), status(k+1), history(k)] | history(k)] \
            &+ mean(P) [I(event(k+1) <= tau, status(k+1) = ell) mean(P) [sum_(j=k+2)^K I(event(j) <= tau, status(j) = y) | history(k+1)] | history(k)] \
    $
    by the law of iterated expectations and that
    $
        (event(k) <= tau, status(k) = y) subset.eq (event(j) <= tau, status(j) in {a, ell})
    $
    for all $j = 1, dots, k-1$ and $k = 1, dots, K$.
] 

#theorem("Identification via g-formula")[
    Let $Qbar(k) = Qbarmiss(k)(Q)$ be defined as in the previous theorem for $Q$.
    Let
    $
        & p_(k a) (t | history(k-1)) \
            &= commonintegral(k, t, survivalfunction(k, s, {ell, a, d, y}) hazard(a, s, k)  \
            & #h(1.5cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ), s) \
            &p_(k ell) (t | history(k-1)) \
            &= commonintegral(k, t, survivalfunction(k, s, {ell, a, d, y}) hazard(ell, s, k) \ \
                & #h(1.5cm) times (integral_(cal(L)) Qbar(k+1) (l_k, treat(k-1), s, ell, history(k-1)) densitycov(s, l_k, k) nu_L (upright(d) l_k) ), s) \
            &= commonintegral(k, t, survivalfunction(k, s, {ell, a, d, y}) hazard(ell, s, k) \
                & #h(1.5cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] ), s) \ \
            & p_(k y) (t | history(k-1)) \ &= commonintegral(k, t, survivalfunction(k, s, {ell, a, d, y}) hazard(y, s, k), s) 
    $
    Then, we can identify $Qbar(k)$ via the intensities as
#math.equation(block: true, numbering: "(1)")[$
    Qbar(k) &= p_(k a) (tau | history(k-1)) + p_(k ell) (tau | history(k-1)) + p_(k y) (tau | history(k-1))
$] <eq:cuminc>
Alternatively, we can apply inverse probability of censoring weighting to obtain
    #math.equation(block: true, numbering: "(1)")[$
        Qbar(k-1) &= mean(P) [I(event(k) <= tau, status(k) = ell)/(exp(-integral_(event(k-1))^(event(k)) lambda^c (s | history(k)) upright(d) s)) Qbar(k)(treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
            &#h(1.5cm) + I(event(k) <= tau, status(k) = a) /(exp(-integral_(event(k-1))^(event(k)) lambda^c (s | history(k)) upright(d) s)) \
            &#h(2.5cm) times integral Qbar(k) (a_k, covariate(k-1), event(k), status(k), history(k-1)) densitytrtint(event(k), a_k, k-1) nu_A (upright(d) a_k) \
            &#h(1.5cm) + I(event(k) <= tau, status(k) = y) /(exp(-integral_(event(k-1))^(event(k)) lambda^c (s | history(k)) upright(d) s)) mid(|) history(k-1)]
    $] <eq:ipcw>
    for $k = K-1, dots, 1$. This is Method 3.
    Then, 
    $
        Psi_tau lr((Q)) = mean(P) [ integral  Qbar(0) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)].
    $
]
#proof[The theorem is an immediate consequence of @thm:jointdensity and @thm:parameter (the sets $(event(k) <= t, status(k) = x, covariate(k) in bb(L), treat(k) in bb(A))$ fully determine the regular conditional distribution of $(event(k), status(k), covariate(k), treat(k))$ given $history(k-1)$).]

Interestingly, @eq:cuminc corresponds exactly with the target parameter of @rytgaardContinuoustimeTargetedMinimum2022
and @gill2023causalinferencecomplexlongitudinal by plugging in the definitions of $Qbar(k)$ and simplifying
(to be shown).

We recommend combining Method 2 to deal with high-dimensional confounding initially. Afterwards when there is sparsity use Method 1.

= Implementation of Method 2

First, we rewrite to the interarrival times. Note that the hazard of the interarrival time $S_(k) = T_(k)-T_(k-1)$ is $lambda^x (w+event(k-1) | history(k-1))$
$
    Qbar(k) &= commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(a, s, k)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ), s) \
        &+ commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(ell, s, k) \
            & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] ), s) \
        &+ commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(y, s, k), s) \
        &= integral_(0)^(tau-event(k-1)) exp(- sum_(x = a, ell, y, d) integral_(0)^ (s) lambda^x (w+event(k-1) | history(k-1)) upright(d) w) \
        &times (hazard(a, event(k-1) + s, k) integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, event(k-1) + s, a, history(k)) densitytrtint(event(k-1) + s, a_k, k) nu_A (upright(d) a_k) \
            &+ hazard(ell, event(k-1) + s, k) (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =event(k-1) + s , status(k) = ell, history(k-1)] ) \
                &+ hazard(y, event(k-1) + s, k) )) \
$

Now by using a piecewise estimator of the cumulative hazard, such as the Nelson-Aalen estimator, Cox model, or a random survival forest.
Let $M^x_k  = {i in {1, dots, n} | D_((k),i) = x}$. Let $S_((k),i)$ be the time of the $i$'th event (ordered) in the sample.
Then we can estimate the cumulative hazard for the interarrival times as
$
    hat(Lambda_(k, t)^x) (f_(k-1))= sum_(i in M_k^x) I(S_((k),i-1) < t <= S_((k), i)) hat(A)_(i,k)^x (f_(k-1))
$
for values $hat(A)_(i,k)^x$ that are estimated from the data. Let $c^x_k (t) = sup {i in M_k^x | T_(k,i) <= t}$.
Then we can estimate the integrals in @eq:cuminc, for example the integral corresponding to covariate change,
$
    & sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (f_(k-1)))  (hat(bb(E)_P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) = t_(k-1) + S_((k),i), status(k) = ell, history(k-1) = f_(k-1)] ) \
        &(hat(A)_(i,k)^ell - hat(A)_(i-1,k)^ell) (f_(k-1))
$
for given covariate history.

We begin with an algorithm for Method 2, in which it is initially assumed that all relevant models can be fitted.

== Surrogate/approximate modeling of the $macron(Q)$ function
Let $K_tau$ be the maximal number of non-terminal events that occur before time $tau$.
We suppose we are given estimators $hat(Lambda)_k (t)^x$ of the cause-specific hazard functions for the interarrival times $S_(k) = event(k) - event(k-1)$,
which are piecewise constant. 

1. Let $cal(R)^y_(K, tau) = {i in {1, dots, n} | D_((K),i) in {a, ell}, T_((K), i) <= tau, D_((K), i) = y}$. 
2. Calculate for each $j in cal(R)_(K, tau)$, $hat(p)_(K y) = sum_(i=1)^(c^y_K (tau)) exp(- sum_(x = y, d) hat(Lambda)^x_K (cal(F)^j_(T_(K)))) (hat(Lambda)^y_K (cal(F)^j_(T_(K))) - hat(Lambda)^y_K (cal(F)^j_(T_(K-1))))$.
3. Use surrogate model $tilde(p)_(K y)$ for $hat(p)_(K y)$ to learn $p_(K a)$ and thus $macron(Q)_K$.

For each event point $k = K-1, dots, 1$:
1. For each $j in cal(R)_(k, tau)$, calculate $hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$ as earlier.
   Also, calculate $hat(p)_(k a) (tau | cal(F)^j_(T_(k-1)))$ and $hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1)))$
   based on the surrogate model $tilde(Q)_(k+1)$.

At baseline $k = 0$:
1. Calculate $hat(Psi)_n = 1/n sum_(i=1)^n Qbar(0) (A_0, L^i_0)$.
   
#algorithm({
  import algorithmic: *
    Function("Iterative conditional expectation approach (Method 2)", {
    For(cond: $k = K_tau, dots, 1$, {
        Assign($cal(R)_(k, tau)$, ${i in {1, dots, n} | D_((k-1),i) in {a, ell}, T_((k-1), i) <= tau}$)
        Cmt[Obtain $hat(A)_(i,k)^x (f_j)$ for all pairs $i, j in cal(R)_(k, tau)$, $x in {a, ell, y, d}$ by regressing $(S_((k)), D_((k)) = x)$ on $history(k-1)$]
        If(cond: $k < K_tau$, {
            Cmt[Obtain from $tilde(Q)_(k)$ predictions for each $i in cal(R)_(k, tau) sect {i | D_((k),i) = ell}$. Regress these on $event(k), status(k) = ell, history(k-1)$ to get $hat(mu) (event(k), history(k-1))$, an estimator of $bb(E)_P [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = ell, history(k-1)]$. ]
        })
        For(cond: $j in cal(R)_(k, tau)$, {
            Assign($hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$, $sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1)))) (hat(A)_(i,k)^y (cal(F)^j_(T_(k-1))) - hat(A)_(i-1,k)^y (cal(F)^j_(T_(k-1))))$)
            Assign($hat(p)_(k a) (tau | cal(F)^j_(T_(k-1)))$, $bb(1) {k < K_tau} sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1)))) tilde(Q)_(k) (A_k := 1, L^i_k, D^i_k, S_(k,i,j)+ T^i_((k-1)), cal(F)^j_(T_(k-1))) (hat(A)_(i,k)^a (cal(F)^i_(T_(k-1))) - hat(A)_(i-1,k)^a (cal(F)^i_(T_(k-1))))$)
            Assign($hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1)))$, $bb(1) {k < K_tau} sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1))))  hat(mu) (S_(k,i,j)+ T^i_((k-1)), cal(F)^j_(T_(k-1))) (hat(A)_(i,k)^ell (cal(F)^i_(T_(k-1))) - hat(A)_(i-1,k)^ell (cal(F)^i_(T_(k-1))))$)
            Assign($hat(p) (tau | cal(F)^j_(T_(k-1)))$, $hat(p)_(k a) (tau | cal(F)^j_(T_(k-1))) + hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1))) + hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$)
        })
        Cmt[Regress the predicted values $hat(p) (tau | cal(F)^j_(T_(k-1)))$ on $history(k-1)$ to get $tilde(Q)_(k-1)$; the surrogate model for $Qbar(k-1)$]
      })
    })
    Cmt[From $tilde(Q)_0$ obtain predictions for each $i = 1, dots, n$ and regress on $A_0, L_0$; thereby obtaining $1/n sum_(i=1)^n hat(bb(E)_P) [Qbar(0) (A_0, L_0) | A_0 = 1, L^i_0]$ as an estimator of $Psi_tau lr((Q))$]
    // Apply baseline regression    
    Return[*null*]
  })
})
         
= Implementation of the Iterative Conditional Expectations formula

We assume that $K_tau$ is the 1 + the maximal number of
non-terminal events that occur before time $tau$. For now, we assume
that this is number is fixed and does not depend on the sample.
Let $tilde(Y)_k (t) = I (event(k-1) < t <= event(k))$.

For $k = K_tau - 1, dots, 0$:
- We want a prediction function $Qbar(k)$ of the history up to the $k$'th event, that is
  $Qbar(k) : cal(H)_k --> RR$, given that we have one for the $(k + 1)$’th event, i.e.,
  $Qbar(k+1) : cal(H)_k --> RR$ (note that for $k = K_tau$, we have
  $Qbar(K_tau) = I (event(K_tau) <= tau, status(K_tau) = y)$.).
  We consider the data set $cal(D)_(k, n)$ that is obtained from the
  original data $cal(D)_n$ by only considering the observations that have
  had $k$ non-terminal events, that is
  $status(k) in {a, ell}$ for $j = 1, dots, k$. On this data:
    - We estimate $hazard(c, dot, k + 1)$ by using $event(k + 1)$ as the time-to-event and $status(k+1)$ as the event
      indicator on the data set $cal(D)_(k, n)$, regressing on
      $history(k) = (covariate(k), treat(k), event(k), status(k), dots, covariate(0), treat(0))$#footnote[ We abuse the notation a bit by writing $history(k)$
          here, but it is actually a $sigma$-algebra.]
  We are now able provide estimated values for the integrand in @eq:ipcw.
  These values are provided on the smaller data set $cal(D)_(k, n, tau)$
  of $cal(D)_(k, n)$ where we only consider the observations with
  $event(k) <= tau$. This is done as follows:
    1. For observations in $cal(D)_(k, n, tau)$ with $status(k + 1) = ell$ and $event(k + 1) <= tau$, use the previous function
       to predict values $Qbar(k+1)(covariate(k+1), treat(k), event(k+1), status(k+1), history(k))$.
    2. For observations in $cal(D)_(k, n, tau)$ with $status(k + 1) = a$ and $event(k + 1) <= tau$, 
       integrate using the previous function $integral_(cal(A)) Qbar(k+1)(covariate(k), a_k, event(k+1), status(k+1), history(k)) densitytrtint(event(k+1), a_k, k) nu_A (upright(d) a_k)$.
       If for example the intervention sets the treatment to 1, then
       $integral_(cal(A)) Qbar(k+1)(covariate(k), a_k, event(k+1), status(k+1), history(k)) densitytrtint(event(k), 1, k) nu_A (upright(d) a_k) = Qbar(k+1)(covariate(k), 1, event(k), status(k), history(k))$.
       This gives predicted values for this group.
    3. For observations in $cal(D)_(k, n, tau)$ with $status(k + 1) = y$ and $event(k + 1) <= tau$, simply put the values equal to 1.
    4. For all other observations put their values equal to 0.
  For all the observations, divide the corresponding values by
  estimates of censoring survival function $exp(-integral_(event(k))^(event(k+1)) lambda^c (s | history(k)) upright(d) s)$.
  We then regress the values on $history(k) = (covariate(k), treat(k), event(k), status(k), dots, covariate(0), treat(0))$.
  From this regression, we set $Qbar(k)$ to be the predicted values of the
  function from the regression.
- If $k = 0$: We estimate the target parameter via
  $bb(P)_n [sum_(k=1)^(K_tau) Qbar(0) (dot, a_0) nu_A (upright(d) a_0)]$.

*Note*: The $Qbar(k)$ have the interpretation of the
heterogenous causal effect after $k$ events.

For now, we recommend @eq:ipcw for estimating $Qbar(k)a$: For estimators of
the hazard that are piecewise constant, we would need to compute
integrals for each unique pair of history and event times occurring
in the sample at each event $k$. On the other hand, the IPCW approach is very
sensitive to the specification of the censoring distribution. Something
very similar can be written down when we use @eq:cuminc.

== Alternative nuisance parameter estimators
An alternative is to estimate the entire cumulative hazards $Lambda^x$ at once instead of having $K$ separate parameters:
There are very few methods for marked point process estimation but see @liguoriModelingEventsInteractions2023 for methods mostly based on neural networks
or @weissForestBasedPointProcess2013 for a forest-based method. As a final alternative, we can use temporal difference learning to avoid iterative estimation of $macron(Q)^a, tilde(Q)$ @shirakawaLongitudinalTargetedMinimum2024.
Most point process estimators are actually on the form given in terms of ref:intensity. 

= The efficient influence function
We want to use machine learning estimators of the nuisance parameters,
so to get inference we need to debias our estimate with the efficient influence function, e.g., double/debiased machine learning @chernozhukovDoubleMachineLearning2018 or
targeted minimum loss estimation @laanTargetedMaximumLikelihood2006. We use @eq:ipcw for censoring to derive the efficient influence function, because it will contain fewer martingale terms.
Let $N_k^c (t) = N_t ({c} times cal(L) union {emptyset} times cal(A) union {emptyset})$.

#theorem("Efficient influence function")[
    Let $N_k^x = N_t ({x} times cal(L) union {emptyset} times cal(A) union {emptyset})$ and $tilde(Y)_(k-1) (t) = I (event(k-1) < t <= event(k))$.
    The efficient influence function is given by
    #text(size: 7.5pt)[$
        phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), treat(j), j-1)))^(I(status(j) = a))
        (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) \
            & times lr(\[(macron(Z)^a_(k,tau) - Qbar(k-1) (tau, history(k-1))) \
                & + integral_(event(k - 1))^tau (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(exp(- integral_(event(k-1))^u sum_(x=a, ell, d, y, c) hazard(x, s, k- 1) upright(d) s))
            (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s) \]) \
            &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)- Psi_tau (P) 
    $]
    (we take the empty sum to be zero and define $T_0 = 0$, $status(0) = a$ and $history(-1) = L(0)$.)
]

#proof[
    Define (sorry about the notation!)
    // inner part of Q
    $
        macron(Z)^a_(k,tau) (s, t_k, d_k, l_k, a_k, f_(k-1)) &= I(t_k <= s, d_k = ell)/(exp(-integral_(t_(k-1))^(t_k) lambda^c (s | f_(k-1)) upright(d) s)) Qbar(k)(a_(k-1), l_k, t_k, d_k, f_(k-1)) \
            &#h(1.5cm) + I(t_k <= s, d_k = a) /(exp(-integral_(t_(k-1))^(t_k) lambda^c (s | f_(k-1)) upright(d) s)) \
            &#h(2.5cm) times integral Qbar(k) (tilde(a)_k, l_(k-1), t_k, d_k, f_(k-1)) densitytrtint(t_k, tilde(a)_k, k-1) nu_A (upright(d) tilde(a)_k) \
            &#h(1.5cm) +  I(t_k <= s, d_k = y)/(exp(-integral_(t_(k-1))^(t_k) lambda^c (s | f_(k-1)) upright(d) s)), s <= tau
    $
    and let 
    $
        Qbar(k-1) (s) = mean(P) [macron(Z)^a_(k,s) (tau, event(k), status(k), covariate(k), treat(k), history(k-1)) | history(k-1)], s <= tau
    $
    We compute the efficient influence function by taking the Gateaux derivative of the above with respect to $P$,
    by discretizing the time.
    We will use two well-known "results" for the efficient influence function. 
    $
        &partial / (partial epsilon) integral_(event(k-1))^t lambda^x_epsilon (s | history(k-1)) upright(d) s \
            &= (delta_(history(k-1)) (f_(k-1)))/P(history(k-1) = f_(k-1)) integral_(event(k-1))^t 1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^x (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(x, s, k-1) upright(d) s)
    $
    and
    $
        partial / (partial epsilon) lr(mean((1-epsilon)P + epsilon delta_((Y, X))) [Y | X = x] bar.v)_(epsilon = 0) = (delta_(X) (x)) / P(X = x) (Y - mean(P) [Y | X = x])
    $
    We will recursively calculate the derivative,
    $
        partial / (partial epsilon) lr(macron(Q)^(a,epsilon)_(k - 1, tau) (a_(k-1), l_(k-1), t_(t-1), d_(k-1), f_(k-2)) ((1-epsilon)P + epsilon delta_(history(k-1))) bar.v)_(epsilon = 0)
    $
    where we have introduced the notation for the dependency on $P$.
    Then, taking the Gateaux derivative of the above yields,
    $
        & partial / (partial epsilon) lr(macron(Q)^(a,epsilon)_(k - 1, tau) (a_(k-1), l_(k-1), t_(t-1), d_(k-1), f_(k-2)) ((1-epsilon)P + epsilon delta_(history(k-1))) bar.v)_(epsilon = 0) \
            &= delta_(history(k-1) (f_(k-1)))/P(history(k-1) = f_(k-1))  (macron(Z)^a_(k,tau) - Qbar(k-1) (tau, history(k-1)) + \            
            &+ integral_(event(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_(event(k-1))^(t_k) 1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s) \
            &#h(1.5cm) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1))) \
            &+ integral_(event(k-1))^(tau) (I(t_k <= tau, d_(k) in {a, ell})/(exp(-integral_(event(k-1))^(t_(k)) lambda^c (s | f_(k-1)) upright(d) s)) dot ((densitytrtint(t_(k), a_(k), k-1)) / (densitytrt(t_(k), a_(k), k-1)))^(I(d_(k) = a)) partial / (partial epsilon) lr(macron(Q)^(a,epsilon)_(k - 1, tau) (a_(k), l_(k),t_(k), d_(k), f_(k-1)) ((1-epsilon)P + epsilon delta_(history(k))) bar.v)_(epsilon = 0) \
            &#h(1.5cm) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1)) 
    $
    Now note for the second term, we can write
    $
        &integral_(event(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_(event(k-1))^(t_k) 1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s) \
            &#h(1.5cm) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1))) \
        &= integral_(event(k-1))^(tau) integral_(s)^tau macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1)) \
            &#h(1.5cm)1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s)) \
            &= integral_(event(k-1))^(tau) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
                &#h(1.5cm)1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s)) \
    $
    by an exchange of integerals. Combining the results iteratively gives the result.
]
For now, we recommend using the one step estimator and not the TMLE because the martingales are computationally intensive to estimate.
This means that multiple TMLE updates may not be a good idea. 

== Remainder term with IPCW for $K=1$:

Let $phi_(tau,1)$ be the term of the efficient influence function without the martingale
and let $phi_(tau,2)$ be the martingale term.

It is given by

$
    phi_tau^*(P) &= (pi^*(A(0) | L(0))) / (pi(A(0) | L(0))) \
        & times lr(\[ (bb(1){event(1) <= tau, status(1) = y}) / (exp(-Lambda^c (event(1) | A_0, L_0))) - F_1(tau | A_0, L_0) \
            & + integral_(0)^tau (F_1(tau | A_0, L_0) - F_1(s | A_0, L_0)) 1/(exp(-(Lambda^y (s | A_0, L_0)+Lambda^c (s | A_0, L_0))))
            (N^c (upright(d) s) -  tilde(Y) (s) Lambda^c (d s | A(0), L(0))) \]) \
        &+ integral F_1(tau|a, L(0)) pi^*(a | L(0)) nu_A (upright(d) a)- Psi_tau (P)
$
Taken the mean with respect to $P_0$ gives
$
    bb(E)_(P_0) [phi_tau^*(P)] &= bb(E)_(P_0) [(pi^*(A(0) | L(0))) / (pi(A(0) | L(0))) \
        & times lr(\[ (bb(1){event(1) <= tau, status(1) = y}) / (exp(-Lambda^c (event(1) | A_0, L_0))) - F_1(tau | A_0, L_0) \
            & + integral_(0)^tau (F_1(tau | A_0, L_0) - F_1(s | A_0, L_0)) 1/(exp(-(Lambda^y (s | A_0, L_0)+Lambda^c (s | A_0, L_0))))
            (N^c (upright(d) s) -  tilde(Y) (s) Lambda^c (d s | A(0), L(0))) \]) \
        &+ integral F_1(tau|a, L(0)) pi^*(a | L(0)) nu_A (upright(d) a)- Psi_tau (P)] \
        & = bb(E)_(P_0) [(pi^*(A(0) | L(0))) / (pi(A(0) | L(0))) \
            & times lr(\[ (integral_0^tau Lambda^y_0 ( d s | A_0, L(0)) (exp(-Lambda^y_0 (s | A_0, L(0)) - Lambda^c_0 (s| A_0, L(0) ))) (1/ (exp(-Lambda^c (s | A_0, L_0))) - 1/ (exp(-Lambda_0^c (s | A_0, L_0)))) \
            & + integral_(0)^tau (F_1(tau | A_0, L_0) - F_1(s | A_0, L_0)) (exp(-(Lambda_0^y (s | A_0, L_0)+Lambda_0^c (s | A_0, L_0))))/(exp(-(Lambda^y (s | A_0, L_0)+Lambda^c (s | A_0, L_0))))
            (Lambda^c_0 (upright(d) s | A(0), L(0))) -  Lambda^c (d s | A(0), L(0))) \]) \
        &+ integral F_1(tau|a, L(0)) pi^*(a | L(0)) nu_A (upright(d) a)- Psi_tau (P)]
$

and the two parameters are $Psi_tau(P) = bb(E)_P [bb(E)_P ( I(T <= tau, D= y)) / exp(-Lambda))]$.

Let us try to calculate this remainder for a simple static intervention. 

$
    R_2(P,P_0) &= Psi_tau (P)-Psi_tau (P_0) + P_0 (phi_tau^*(P)) \
        &= Psi_tau (P) - Psi_tau (P,S^c_0) + P_0 (phi_(tau,1)^*(P))-P_0 (phi_(tau,1)^*(P, S_0^c)) \
        &+ Psi_tau (P,S^c_0) - Psi_tau (P_0) + P_0 (phi_(tau,1)^*(P, S_0^c)) \
        &+P_0 (phi_(tau,2)^*(P))-P_0 (phi_(tau,2)^*(P, S^c_0)) + P_0 (phi_(tau,2)^*(P, S^c_0))
$
The above calculation shows $P_0 (phi_(tau,2)^*(P, S^c_0)) = 0$.
The martingale difference has the desired product structure (almost we're missing like a 1 in the censoring survival functino quotient).
We can write for one of the terms in the $P_0 (phi_(tau,1)^*(P))-P_0 (phi_(tau,1)^*(P, S_0^c))$:
$
    P_0[ bb(E)_P [I(T <= tau, D = 1) / (S^c (T| 1, L)) - I(T <= tau, D = 1) / (S_0^c (T| 1, L)) | A_0 = 1, L]]
$
For the other term
$
    P_0[ (bb(1) {A=1}) / (pi(A, L)) bb(E)_P [I(T <= tau, D = 1) / (S^c (T| 1, L)) - I(T <= tau, D = 1) / (S_0^c (T| 1, L)) | A_0 = 1, L]]
$
Add these two terms to get

For the other term in the $phi_(tau,1)$, we have $P_0 (phi_(tau,1)^*(P, S_0^c)) = 0$.
//$
//    Psi_tau (P,S^c_0) - Psi_tau (P_0) = bb(E)_P [bb(E)_P [I(T <= tau, D = 1) / (S^c (T| 1, L)) - I(T <= tau, D = 1) / (S_0^c (T| 1, L)) | A_0 = 1, L] ]
//$
Apply the well-known remainder when the censoring is known to the second term to get
$
    (2) = integral (pi (1 | L) - pi_0(1|L))/(pi (1|L)) (bb(E)_P [I(T <= tau, D = 1) / (S_0^c (T| 1, L)) | A_0 = 1, L]-bb(E)_(P_0) [I(T <= tau, D = 1) / (S_0^c (T| 1, L)) | A_0 = 1, L]) d P_0 (L)
$
We get a term like (2) for the other part.

== Comparison with the EIF in @rytgaardContinuoustimeTargetedMinimum2022
Let $B_(k-1) (u) = (Qbar(k-1)(tau) -Qbar(k-1)(u)) 1/exp(-sum_(x=a,ell,d,y) integral_(event(k-1))^u hazard(x, w, k-1) upright(d) w)$
and $S (u | history(k-1)) = exp(-sum_(x=a,ell,d,y) integral_(event(k-1))^u hazard(x, w, k-1) upright(d) w)$ and $S^c (u | history(k-1)) = exp(- integral_(event(k-1))^u hazard(c, w, k-1) upright(d) w)$.
We claim that the efficient influence function can also be written as:
$
    phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), treat(j), j-1)))^(I(status(j) = a)) (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) [ \
        &integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)- B_(k-1) (u)) M_k^(a) (d u) \
         &+integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] - B_(k-1) (u)) M_k^(ell) (d u) \
         &+integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (1 - B_(k-1) (u)) M_k^(y) (d u) +integral_(event(k-1))^tau 1/(S^c (u | history(k-1)))(0 - B_(k-1) (u)) M_k^(d) (d u) \
        &+  1/(S^c (event(k) | history(k-1))) I(event(k) <= tau, status(k) = ell, k < K)( Qbar(k) (covariate(k), treat(k-1), event(k), ell, history(k-1)) \
                            &#h(1.5cm) - mean(P) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = event(k) , status(k) = ell, history(k-1)] )]\
                        &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)- Psi_tau (P) 
$

We find immediately that

$
    phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), treat(j), j-1)))^(I(status(j) = a)) (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) [ \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)) Lambda_k^(a) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) Lambda_k^(ell) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (1) Lambda_k^(y) (d u) -integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)))(0) Lambda_k^(d) (d u) \
                & -integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^bullet (upright(d) u) \
        &+ macron(Z)_(k,tau) (event(k), status(k), covariate(k), treat(k), history(k-1)) + integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^c ( d u)] \
                &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)- Psi_tau (P)
$
Now note that 
$
    & integral_(event(k - 1))^tau (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) (N^bullet_k (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(bullet, s, k-1) upright(d) s) \   
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
        &+ integral_(event(k-1))^(tau and event(k)) (Qbar(k-1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
$
Let us calculate the second integral
$
    & Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
    &= Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) (S^c (u | history(k-1)) S (u | history(k-1)))/(S^c (u | history(k-1)) S (u | history(k-1)))^2 hazard(bullet, s, k-1) upright(d) s \
        &= Qbar(k-1)(tau) (1-1/(S^c (event(k) and tau | history(k-1)) S (event(k) and tau | history(k-1))))
$
where the last line holds by the Duhamel equation (or using that the antiderivative of $- f' / f^2$ is $1/f$).
The first of these integrals is equal to
$
    &integral_(event(k-1))^(tau and event(k)) (Qbar(k+1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u \
        &= integral_(event(k-1))^(tau and event(k)) [integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
            &+  integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, y, d s)]  \
        &times 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u \
        &= integral_(event(k-1))^(tau and event(k)) integral_(s)^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u [S(s | history(k-1)) cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+ S(s | history(k-1)) cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
            &+  S(s | history(k-1)) cumhazard(k-1, y, d s)]
$
Now note that
$
    & integral_(s)^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u \
    &= 1/(S^c (s) S (s)) - 1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) 
$
Setting this into the previous integral, we get
$
    &integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) upright(d) u [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] \
        &- 1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) Qbar(k-1) (tau and event(k))
$
Thus, we find
$
    & integral_(event(k - 1))^tau (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) (N^bullet_k (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(bullet, s, k-1) upright(d) s) \   
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
        &+ integral_(event(k-1))^(tau and event(k)) (Qbar(k-1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-(Qbar(k-1)(tau) (1-1/(S^c (event(k) and tau | history(k-1)) S (event(k) and tau | history(k-1))))) \
        &+integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) upright(d) u [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] \
        &- 1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) Qbar(k-1) (tau and event(k)) \
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &+(Qbar(k-1)(tau)- Qbar(k-1)(tau and event(k)))/(S^c (event(k) and tau | history(k-1)) S (event(k) and tau | history(k-1))) \
        &+integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) upright(d) u [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] -Qbar(k-1)(tau)  \
        &=^? integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) upright(d) u [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] -Qbar(k-1)(tau) 
$
Inserting this into the EIF gives the desired result in terms of our EIF. 

= Data-adaptive choice of $K$
In practice, we will want to use $K_tau$ to be equal to 1 + maximum number of non-terminal events up to $tau$ in the sample. 
It turns out, under the boundedness condition of the number of events,
that an estimator that is asymptotically linear with efficient influence function $phi_tau^*(P) (max_i kappa_i (tau))$
is also asymptotically linear with efficient influence function $phi_tau^*(P) (K_tau)$
where $K_tau$ is the last event point such that $P(kappa_i (tau) = K_tau) > 0$.

Sketch: We want to use $K = K_n = max_i kappa_i (tau)$.
If we can do asymptotically and efficient inference for $K_n$, then we can also do it for a limiting $K_n <= K$.
Assume that the estimator is asymptotically linear with efficient influence function $phi_tau^*(P) (K_n)$.
Then by Assumption 1, there exists a $K_lim$ which is the last point such that $P(K_n = K_lim) > 0$.
Then, $K_n$ converges to $K_lim$ (by independence), and moreover, under standard regularity conditions such as strict positivity,
$
    (bb(P)_n-P) ( phi_tau^*(P) (K_n) - phi_tau^*(P) (K))
$ is $o_P(n^(-1/2))$, so if have asymptotic linearity in terms of $phi_tau^*(P) (K_n)$, then we automatically have it
for the original estimator for $phi_tau^*(P) (K_lim)$

= Issues relating to rare patient histories (postponed)
Consider the following table representing example data:

#figure(
table(
  columns: 7,
    [$k$], [0], [1], [2], [3], [4], [5],
    [$tilde(Y)_k (tau)$],   [10000], [8540], [5560], [2400], [200], [4],
    [$Delta treat(k)$],     [6000],  [3560], [1300],  [100],  [2], [NA],
    [$Delta covariate(k)$], [2540],  [2000], [1100], [100],  [2], [NA]
))
== Pooling

Some people have complex histories. There may be very few of these people in the sample,
so how do we do estimate the cause-specific hazard for the censoring in, say, the first step?
In the artificial data example, there are only 4 people at the last time point. 

We propose to pool the regressions across event points:
Let us say that we want to estimate the cause-specific hazard for the censoring at event $k+1$
among people who are at risk of being censored at the $k+1$'th event, that is
they either had a treatment change or a covariate change at their $k$ event.
If this population in the sample is very small, then we could do as follows.
We delete the first event for these observations. Then
the number of covariates is reduced by one, so we have the same number of covariates
as we did for the people who are at risk of having an event at the $k$'th event.
We combine these two data sets into one and regress the cause-specific hazard for the censoring at event "$k$".
This provides a data set with correlated observations,
which likely is not biased as we are not interested in variance estimation for parameters appearing in the regression.

To estimate the regression for the time-varying covariates, one could do:
- Not intervene on the last two or three time points, letting certain parts of the data generating mechanism be observational,
  that is $densitytrtint(t, dot, j) = densitytrt(t, dot, j)$ for $j = 4, 5$.
- Another is to make a Markov-like assumption in the interventional world, i.e.,
  $
      mean(Q) [ sum_(j=1)^3 I(event(j) <= tau, status(j) = y) | history(0)] = mean(Q) [sum_(j=6)^8 I(event(j) <= tau, status(j) = y) | history(5)]
  $
  So we separately estimate the target parameter on the left hand side and use it to estimate the one on the right when we need to,
  pooling the data from the last three events with the data from the first three events.

Doing this adaptively leads to data-adaptive target parameter #citep(<hubbard2016statistical>).

// The most unfortunate situation-wise is that:
// #figure(
// table(
//   columns: 3,
//     [$k$], [0], [1], 
//     [$tilde(Y)_k (tau)$],   [10000], [8004],
//     [$Delta treat(k)$],     [8000],  [...],
//     [$Delta covariate(k)$], [4],  [...]
// ))
// In this case, we can forget about using iterative regression -- what we used previously is
// that the only point of sparsity was after many events. 
// Here we would need to estimate the conditional density of $densitycov(t, dot, 1)$ instead of regressing
// -- this could be done by once again pooling, but may be very hard to do computationally because the estimation of a conditional
// density is much, much harder than regression.

Other possible methods are:

- Use an estimation procedure that is similar to @shirakawaLongitudinalTargetedMinimum2024 or use hazards which are estimated all at once.

- Bayesian methods may be useful since they do not have issues with finite sample size. They are also a natural way of dealing with the missing data problem.
  However, nonparametric Bayesian methods are not (yet) able to deal with a large number of covariates.

== Other ideas
Some other issues are that the covariates are (fairly) high dimensional.
This may yield issues with regression-based methods. 

- Use Early-stopping cross-validation described as follows:
  First fit models with no covariates.
  Then we fit a model with the covariates from the last event.
  Determine if this is improves model fit via cross-validation and then we move on to the two latest changes and so on.
  Stop when the model fit does not improve. Theorem 2 of @schulerSelectivelyAdaptiveLasso2022 states that the convergence rates for an empirical risk minimizer are preserved.
  CTMLE also does something very similar #citep(<van2010collaborative>).
  This way, we may only select variables that are important in the specification of the treatment and outcome mechanism.

== Topics for further research

Interestingly, $integral Qbar(0) (a, covariate(0)) nu_A (upright(d) a)$ is a heterogenous causal effect.
Can we estimate heterogenous causal effects in this way?

Time-fixed time-varying treatment could probably be interesting within
a register-based study since it may be easier to define treatment in an interval
rather than two define on, each time point, if the patient is on the treatment or not.

It may also sometimes be the case that some time-varying covariates
are measured regularly instead of at subject-specific times.
In this case, we may be able to do something similar to the above.

#bibliography("references/ref.bib",style: "apa")
