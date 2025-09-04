#import "@preview/touying:0.6.1": *
#import themes.university: *
#import "@preview/theorion:0.3.2": *
#import cosmos.clouds: *
#import "template/graph.typ": *
#import "template/shortcuts_presentation.typ": *
#import "@preview/numbly:0.1.0": numbly

#show: show-theorion
#set cite(form: "prose")
#show: university-theme.with(
  aspect-ratio: "16-9",
   config-common(new-section-slide-fn: none),
  //config-common(handout: true),
  config-common(frozen-counters: (theorem-counter,)),  // freeze theorem counter for animation
  config-info(
    title: [Sequential Regressions for Efficient Continuous-Time Causal Inference],
    author: [Johan Sebastian Ohlendorff],
    institution: [University of Copenhagen],  
    //date: datetime.today(),
  ),
)

#set text(size: 18pt)
//#set math.equation(numbering: "(1)")
#let indep = $perp #h(-1em) perp$ // Independence relation
#let colred(x) = text(fill: red, $#x$)
#let colblue(x) = text(fill: blue, $#x$)
#set heading(numbering: "1.")

#title-slide()

= Who am I?

- PhD student in Biostatistics at the Section of Biostatistics, University of Copenhagen.
#pause
- Supervisors: Thomas Alexander Gerds and Anders Munch.
#pause
- Work on continuous-time longitudinal causal inference using
    - Targeted learning (e.g., TMLE (@laanTargetedMaximumLikelihood2006) or double/debiased machine learning (@chernozhukovDoubleMachineLearning2018)).
#pause
- Working on a continuous-time scale is motivated by:
    - Real-world data often recorded in continuous time (e.g., electronic health records).
    - Avoiding bias due to discretization (@ryalen2019additive @discretization2020guerra @kant2025irregular @sun2023role @adams2020impact @sofrygin2019targeted).
#pause
- We follow the setting in @rytgaardContinuoustimeTargetedMinimum2022
  and are interested in the mean interventional absolute risk under a specified treatment regime in continuous time.
#pause
- *Problem*: @rytgaardContinuoustimeTargetedMinimum2022 do not provide a feasibly implementable procedure for estimation.

= Notation and Setup
- *Study period*: $[0, tau_"end"]$.
#pause
- *Càdlàg, jump processes*
  - Treatment: $A(t) in {0,1}$
  - Covariates: $L(t) in RR^d$
#pause
- *Counting processes*
  - $N^x; x in {a, ell, y}$ (treatment, covariate, death)
  - Observed until censoring time $C$
  - Terminal event time: $T_e$
#pause
- *Assumptions*
  - Jumps in $A(t)$ or $L(t)$ only when corresponding $N^a$ or ($N^ell$ or $N^a$) jump.
  - No simultaneous jumps + orthogonal martingales
#pause
- *Treatment decisions*
  - Doctor chooses treatment at jump times of $N^a$
  - Intervention specifies decision, not timing
#pause
- *Bounded events*
  - Each individual has at most $K$ events in $[0, tau_"end"]$

= Filtrations
$
    cal(F)_t &= sigma((A (s),L (s),N^a (s),N^ell (s),N^y (s)): s <= t) or sigma((A (0),L (0))) \
    #pause
    cal(F)^("full")_t &= sigma((A (s),L (s),N^a (s),N^ell (s),N^y (s), N^c (s)): s <= t) or sigma((A (0),L (0))) \
    #pause
    macron(cal(F))_t &= sigma((A (s and C),L (s and C),N^a (s and C),N^ell (s and C), N^y (s and C), N^c (s and T^e)): s <= t) or sigma((A (0),L (0)))
$
#meanwhile

- $cal(F)_t$: natural filtration for the processes without censoring
#pause
- $cal(F)^("full")_t$: natural filtration for the processes including censoring
#pause
- $macron(cal(F))_t$: observed (natural) filtration
#pause
- Data format (uncensored)
$
    (event(K), status(K), treat(K-1), covariate(K-1), underbrace(T_((K-1)), "ordered event time"), underbrace(status(K-1), in {a,y,ell} \ "status indicator"), dots, treat(0), covariate(0))
$
- Data format (censored)
$
    (eventcensored(K), statuscensored(K), treatcensored(K-1), covariatecensored(K-1), eventcensored(K-1), statuscensored(K-1), dots, treat(0), covariatecensored(0))
$

= Target parameter (no censoring)
- *Random measure*
  $N_t^(a *)$: random measure associated to $N_a$ and $A$ given by
$
      N_t^(a *) = sum_(k: status(k) = a) delta_((event(k), treat(k)))
$
#pause
- *Intervention*
  - Modify compensator: $Lambda^(a *)_t (dot)= pi_t (dot) Lambda^a (t)$
  - Replace treatment mechanism 
    - $pi_t ({x}) = P (A (t) = x | cal(F)_(t-))$
    - Under new law $P^(G^*)$, compensator of $N^a$ is $pi^*_t (dot) Lambda^a (t)$
        with respect to $cal(F)_t$
#pause
- *Special case*
  - $pi_t^* ({x}) equiv bb(1) {x = 1}$ (stay on treatment)
#pause
- *Target parameter*
  - $Psi_tau (P) = bb(E)_(P) [(dif P^(G^*)) / (dif P) (tau) N^y (tau)] = bb(E)_(P^(G^*))[N^y (tau)], tau < tau_"end"$

= Efficient influence function (@rytgaardContinuoustimeTargetedMinimum2022)
- *Efficient influence function (EIF)* for $Psi_tau (P)$ in the nonparametric model is given by
  (@rytgaardContinuoustimeTargetedMinimum2022)
$ 
    phi_tau^*(P) &= mean(P^(G^*)) [N_y (tau) | cal(F)_0] - Psi_tau (P) \
        &+ integral_0^tau (dif P^(G^*)) / (dif P) (t -) (mean(P^(G^*)) [N_y (tau) | L(t), N^ell (t), cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | N^ell (t), cal(F)_(t-)]) tilde(N)^ell (dif t) \
        &+ integral_0^tau (dif P^(G^*)) / (dif P) (t -) (mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 0, cal(F)_(t-)]) tilde(M)^ell (dif t) \
        &+ integral_0^tau (dif P^(G^*)) / (dif P) (t -) (mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 0, cal(F)_(t-)]) tilde(M)^a (dif t) \
        &+ integral_0^tau (dif P^(G^*)) / (dif P) (t -) (1 - mean(P^(G^*)) [N_y (tau) | Delta N^y (t) = 0, cal(F)_(t-)]) tilde(M)^y (dif t).
$
- $tilde(M)^x (t) = tilde(N)^x (t) - Lambda^x (t)$ is the $P$-$macron(cal(F))_t$ martingale for $tilde(N)^x (t) = N^x (t and C)$.

== Efficient influence function (continued)
//- The above EIF suggests an estimation procedure based on sequential regressions.
- To work within the targeted learning framework, we need the efficient influence function.  
#pause
- @rytgaardContinuoustimeTargetedMinimum2022 propose sequential regressions for estimating terms in $phi_tau^* (P)$.
#pause
- Implementation is unclear and may require thousands of iterations (iterate through all unique event times in the sample).  
  // Example: if $n=1000$, with 10 events/person → 10,000 regressions.  
#pause
- *Idea*: Replace $cal(F)_(t-)$ with simpler histories:  
  - $history(k) = sigma(treat(j), covariate(j), event(j), status(j): j <= k) or sigma((A(0), L(0)))$
  - Censored versions:  
    $historycensored(k) = sigma(treatcensored(j), covariatecensored(j), eventcensored(j), statuscensored(j): j <= k) or sigma((A(0), L(0)))$

= Illustration of sequential regressions
#align(center)[
    @rytgaardContinuoustimeTargetedMinimum2022:
    #timegrid2(new_method: false)
    #pause
    ICE-IPCW (@sequentialRegressionOhlendorff):
    #timegrid2(new_method: true)
]

= Consistency of ICE-IPCW (right-censoring)
- *Propensity score*:
  - $densitytrt(t, k)$: $P(treat(k) = 1 | covariate(k), event(k) = t, status(k) = a, history(k-1))$
- *Hazard measures*:
  - $tilde(Lambda)_(k)^c (t | historycensored(k-1))$: hazard measure for $(eventcensored(k), bb(1) {statuscensored(k) = c})$ given $historycensored(k-1)$
  - $cumhazard(k, x, t)$: hazard measure of $(event(k), bb(1) {status(k) = x})$ given $history(k-1)$ for $x in {a, ell, y}$
#pause
- $product$: product integral (@gill1990survey)
#pause
- *Survival functions*:
  - $tilde(S)^c (t | historycensored(k-1)) = product_(s in (eventcensored(k-1), t]) (1 - d tilde(Lambda)_(k)^c (s | historycensored(k-1)))$
  - $S (t | history(k-1)) = product_(s in (event(k-1), t]) (1 - sum_(x=a,ell,y,d) d Lambda_k^x (s | history(k-1)))$
#pause
- *Random measure*:
  - $N = sum_k delta_((event(k), status(k), treat(k), covariate(k)))$
  - Turns out that natural filtration of $N$ is $cal(F)^"full"_t$ (Chapter 2.5 of @last1995marked)
    
== Independent censoring conditions 
- Let $Qbar(K): (a_k, h_k) mapsto 0$
#pause
- Define recursively, for $k = K, dots, 0$,
$
        macron(Z)^a_(k, tau) (u) =
        colblue(1/(tilde(S)^c (eventcensored(k) - | treatcensored(k-1), macron(H)_(k-1)))) &(bb(1) {eventcensored(k) <= u,eventcensored(k) < tau, statuscensored(k) = a}
        Qbar(k) (1, macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, eventcensored(k) < tau, statuscensored(k) = ell} Qbar(k) (treatcensored(k), macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, statuscensored(k) = y}),
$
and
$
   Qbar(k): (u, a_k, h_k) mapsto mean(P) [macron(Z)^a_(k+1, tau) (u) | treatcensored(k) = a_k, macron(H)_(k) = h_k], quad u <= tau
$
where $h_k = (a_k, l_k, t_k, d_k, dots, a_0, l_0)$.

== ICE-IPCW procedure: Consistency
#theorem[
    Assume that the $P$-$cal(F)^"full"_t$ compensator $Lambda$ of $N$ is also the $P$-$cal(F)_t$ compensator of $N$.
#pause
If
    1. $Delta tilde(Lambda)_(k)^c (dot, historycensored(k-1)) Delta cumhazard(k, x, dot) equiv 0$ for $x in {a, ell, y}$ and $k in {1, dots, K}$.
    2. $tilde(S)^c (t | historycensored(k-1)) > eta$ for all $t in (0, tau]$ and $k in {1, dots, K}$ $P$-a.s. for some $eta > 0$.
#pause 
    It holds that 
    $
        Psi_tau^g (P) = mean(P) [Qbar(0) (tau, 1, covariate(0))].
    $ <eq:ice-end>
]
#pause
- We make _explicit_ use of the fact that the compensator can be explicitly written in terms of the regular conditional distributions
  of the variables $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$, $k = 1, dots, K$
  and $(treat(0), covariate(0))$.

= Rewriting the efficient influence function 

#theorem[Under suitable regularity conditions, $phi_tau^* (P)$ can be rewritten as
    $
        phi_tau^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) colblue(1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))))   \
            & times bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} ((macron(Z)^a_(k,tau) (tau)- Qbar(k-1) (tau)) \
                &quad colblue(+ integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1) (tau)-Qbar(k-1) (u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u)))\
            & +  Qbar(0) (tau) - Psi_tau^g (P).
    $
]

= Practical Considerations & Perspectives
- *Estimator*  
  - One-step estimator based on the efficient influence function
#pause 
- *Simulations*
  - Lower bias than LTMLE (@ltmle) and good CI coverage.
  - Mean squared errors are however close to being the same.
- *Application*: Apply to real-world data with Danish registry data:
  - EIF provides confidence intervals comparable to bootstrap CIs.
#pause
- *Challenges*  
  - Variance estimation is difficult (censoring martingale term)  
  - Possible approaches:  
    - Undersmooth estimation of censoring compensator
    - Machine learning (e.g., neural networks) methods for multivariate outcomes (to $Qbar(k) (u)$)
#pause
- *Next steps*
  - Empirical process & remainder term conditions not yet addressed (ongoing work)  
  - Consider TMLE instead of one-step $=>$ ensures estimates in $[0,1]$
  - Apply flexible, data-adaptive estimators for nuisance parameters
  - #text(fill: red, [Clarify causal interpretation of target parameter (identifiability)])
//  - Explore alternative parameters of interest (e.g., recurrent events, restricted mean survival time)  

= Appendix 
#bibliography("references/ref.bib",style: "apa")
