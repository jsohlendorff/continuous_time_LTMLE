#import "@preview/touying:0.6.1": *
#import themes.university: *
#import "@preview/theorion:0.3.2": *
#import cosmos.clouds: *
#import "template/graph.typ": *
#import "template/shortcuts.typ": *
#import "@preview/numbly:0.1.0": numbly

#show: show-theorion
#set cite(form: "prose")
#show: university-theme.with(
    aspect-ratio: "16-9",
   config-common(new-section-slide-fn: none),
  // config-common(handout: true),
  config-common(frozen-counters: (theorem-counter,)),  // freeze theorem counter for animation
  config-info(
    title: [Sequential Regressions for Efficient Continuous-Time Causal Inference],
    author: [Johan Sebastian Ohlendorff],
    date: datetime.today(),
  ),
)

#set text(size: 18pt)
//#set math.equation(numbering: "(1)")
#let indep = $perp #h(-1em) perp$ // Independence relation
#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

= Who am I?

- PhD student in Biostatistics at the Section of Biostatistics, University of Copenhagen.
#pause
- Supervisors: Thomas Alexander Gerds and Anders Munch.
#pause
- Work on continuous-time longitudinal causal inference using
    - Targeted learning (e.g., TMLE @rytgaardContinuoustimeTargetedMinimum2022 or one-step estimation).
    - Efficiency theory.

= Notation and setup
- We observe a càdlàg, jump process for the treatment $(A(t))_(t in [0, tau_"end"]) in {0, 1}$ and a covariate process $(L(t))_(t in [0, tau_"end"])$,
  such that $L (t)$ almost surely takes values some finite subset of $bb(R)^d$.
#pause
- Assume that we are observe the counting processes $N^x$, $x=a,ell,y$ (treatment, covariate, death, censoring)
  up to a right-censoring time $C$ which is distinct from all event times with probability 1. Terminal event time is denoted by $T^e$.
#pause
- Assume that $Delta A (t) != 0$ only if $Delta N^a (t) != 0$ and $Delta L (t) != 0$ only if $Delta N^ell (t) != 0$ or $Delta N^a (t) != 0$.
  #pause It then seems reasonable to assume that $Delta N^a Delta N^ell equiv 0$
  and that, in fact, every counting process does not jump at the same time as any other counting process.
#pause
- The doctor may decide treatment based at times at which $Delta N^a (t) != 0$.
  The intervention in which we are interested attempts to specify what this decision should be (or the probability of being treated),
  but does not naturally intervene on when the doctor decides to do so.
#pause
- Each individual has at most $K$ events in $[0, tau_"end"]$, i.e.,
  $sum_(x=a,y,c,ell) N^x (tau_"end") <= K$ almost surely.

= Filtrations
$
    cal(F)_t &= sigma((A (s),L (s),N^a (s),N^ell (s),N^y (s)): s <= t) \
    #pause
    cal(F)^(beta)_t &= sigma((A (s),L (s),N^a (s),N^ell (s),N^y (s), N^c (s)): s <= t) \
    #pause
    cal(F)^(tilde(beta))_t &= sigma((A (s and C),L (s and C),N^a (s and C),N^ell (s and C), \
        &quad quad N^y (s and C), N^c (s and T^e)): s <= t)
$
#meanwhile

- $cal(F)_t$ is the natural filtration for the processes without censoring.
#pause
- $cal(F)^(beta)_t$ is the natural filtration for the processes including censoring.
#pause
- $cal(F)^(tilde(beta))_t$ is the observed filtration, i.e., the natural filtration stopped by death and censoring.
 
= Target parameter (without censoring)
- Data format:
$
      O = (event(K), status(K), treat(K-1), covariate(K-1), event(K-1), status(K-1), dots, treat(0), covariate(0))
$
#pause
- Let $N_t^a (dot)$ denote the random measure associated with $N^a$ and $A (dot)$,
$
      N_t^a (A) = sum_(k: status(k) = a) delta_((event(k), treat(k))) (A).
$
  
#pause
- Interested on "intervening" on the compensator of $N^a (dot)$.
  Generally, this can be written as
  $Lambda^a_t (A) = pi_t (A) Lambda^a (t)$.
#pause
- The intervention defines a probability measure $P^(G^*)$, where
  $N^a (dot)$ has compensator $pi_t^* (A) Lambda^a (t)$
  for specified $pi_t^* (A)$.
#pause
- Focus on the case $pi_t^* ({x}) equiv bb(1) {x = 1}$.

== Target parameter (continued)

- We are then interested (are we?) in
$
      Psi_tau (P) = bb(E)_(P) [(d P^(G^*)) / (d P) (tau) N^y (tau)] = bb(E)_(P^(G^*))[N^y (tau)]
$
// Hotly contested topic
#pause
- With $W^g (t) = (d P^(G^*)) / (d P) (t)$, @rytgaardContinuoustimeTargetedMinimum2022 claims that the following is the EIF:
$ 
    phi_tau^*(P) &= mean(P^(G^*)) [N_y (tau) | cal(F)_0] - Psi_tau (P) \
        &+ integral_0^tau W^g (t -) (mean(P^(G^*)) [N_y (tau) | L(t), N^ell (t), cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | N^ell (t), cal(F)_(t-)]) tilde(N)^ell (dif t) \
        &+ integral_0^tau W^g (t -) (mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 0, cal(F)_(t-)]) tilde(M)^ell (dif t) \
        &+ integral_0^tau W^g (t -) (mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 0, cal(F)_(t-)]) tilde(M)^a (dif t) \
        &+ integral_0^tau W^g (t -) (1 - mean(P^(G^*)) [N_y (tau) | Delta N^y (t) = 0, cal(F)_(t-)]) tilde(M)^y (dif t).
$

== Sequential regressions
- Here $tilde(M)^x (t) = tilde(N)^x (t) - Lambda^x (t)$ is the martingale for $tilde(N)^x (t) = N^x (t and C)$.
- The above EIF suggests an estimation procedure based on sequential regressions.
#pause
- It is unclear how to estimate $mean(P^(G^*)) [N_y (tau) | Delta N^x (t), cal(F)_(t-)]$.
#pause
- Sequential regression not clear how to implement.
- @rytgaardContinuoustimeTargetedMinimum2022 iterative procedure requires 1000s of iterative steps.
  - Assume that $n=1000$; if all registrations in the sample are unique and each person has 10 events on average, then we need to fit 10,000 regressions.
- Hard to work with $cal(F)_(t-)$. 
#pause
- My idea: Can we work with $history(k) = sigma(treat(j), covariate(j), event(j), status(j): j <= k) or sigma((A(0), L(0)))$ instead
  and more generally $historycensored(k) = sigma(treatcensored(j), covariatecensored(j), eventcensored(j), statuscensored(j): j <= k) or sigma((A(0), L(0)))$
  and regress back on that information instead of $cal(F)_(t-)$?

== Illustration

#timegrid(new_method: false, slides: true)
#pause
#timegrid(new_method: true)

= Results (without censoring)
#theorem[
    #set align(left)
    Let $H_k = (covariate(k), event(k), status(k), treat(k-1), covariate(k-1), event(k-1), status(k-1), dots, treat(0), covariate(0))$ be the history up to and including the $k$'th event,
    but excluding the $k$'th treatment values for $k > 0$. For $k = 0$, let $H_0 = covariate(0)$.
    Let $Qbar(K): (a_k, h_k) mapsto 0$ and recursively define for $k = K-1, dots, 1$,
    $
        Z^a_(k+1, tau) (u) &= bb(1) {event(k+1) <= u, event(k+1) < tau, status(k+1) = ell) Qbar(k+1) (tau, treat(k), H_(k+1)) \
            &qquad+ bb(1) {event(k+1) <= u, event(k+1) < tau, status(k+1) = a) Qbar(k+1) (tau, 1, H_(k+1)) \
            &qquad + bb(1) {event(k+1) <= u, status(k+1) = y), 
    $ 
    and
    $
        Qbar(k): (u, a_k, h_k) mapsto mean(P) [Z^a_(k+1, tau) (u) | treat(k) = a_k, H_k = h_k], 
    $ <eq:ice>
    for $u <= tau$.
    Then,
    $
        Psi_tau^g (P) = mean(P) [Qbar(0) (tau, 1, covariate(0))].
    $ <eq:ice-end>
]

= Independent censoring conditions
Let
$
        macron(Z)^a_(k, tau) (u) =
        1/(tilde(S)^c (eventcensored(k) - | treatcensored(k-1), macron(H)_(k-1))) &(bb(1) {eventcensored(k) <= u,eventcensored(k) < tau, statuscensored(k) = a}
        Qbar(k) (1, macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, eventcensored(k) < tau, statuscensored(k) = ell} Qbar(k) (treatcensored(k), macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, statuscensored(k) = y}).
$
#pause
- $tilde(S)^c (t | historycensored(k-1)) = product_(s in (eventcensored(k-1), t]) (1 - d tilde(Lambda)_(k)^c (s | historycensored(k-1)))$.
#pause
- $tilde(Lambda)_(k)^c (t | historycensored(k-1))$ denotes the hazard measure of $(eventcensored(k), bb(1) {statuscensored(k) = c})$ given $historycensored(k-1)$
  and $cumhazard(k, x, t)$ denotes the hazard measure of $(event(k), bb(1) {status(k) = x})$ given $history(k-1)$ for $x in {a, ell, y, d}$.

= Independent censoring conditions
    Assume that the compensator $Lambda^alpha$ of $N^alpha$ with respect to the filtration $cal(F)^beta_t$ is
    also the compensator with respect to the filtration $cal(F)_t$.
#pause
If
    1. $Delta tilde(Lambda)_(k)^c (t | historycensored(k-1)) + sum_x Delta cumhazard(k, x, t) = 1 quad P-"a.s."=> Delta tilde(Lambda)_(k+1)^c (t | history(k-1)) = 1 quad P-"a.s." or sum_x Delta cumhazard(k, x, t) = 1 quad P-"a.s."$.
    2. $tilde(S)^c (t | historycensored(k-1)) > eta$ for all $t in (0, tau]$ and $k in {1, dots, K}$ $P$-a.s. for some $eta > 0$.
#pause 
    Then with $h_k = (a_k, l_k, t_k, d_k, dots, a_0, l_0)$,
    $
        bb(1) {d_(1) in {a, ell}, dots, d_(k) in {a, ell}} Qbar(k) (u, a_k, h_k) = mean(P) [macron(Z)^a_(k+1, tau) (u) | treatcensored(k) = a_k, macron(H)_(k) = h_k].
    $ <eq:iceipcw>
    Hence $Psi_tau^g (P)$ is identifiable from the observed data.

== Rewriting the efficient influence function 

- $tilde(M)^c (t) = tilde(N)^c (t) - tilde(Lambda)^c (t)$. Here $tilde(N)^c (t) = bb(1) {C <= t, T^e > t} = sum_(k=1)^K bb(1) {eventcensored(k) <= t, statuscensored(k) = c}$ is the censoring counting process.
#pause
- $S (t | history(k-1)) = product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1)))$.
#pause
- Suppose that there is a universal constant $C^* > 0$
  such that $tilde(Lambda)^c_k (tauend | historycensored(k-1); P) <= C^*$ for all $k = 1, dots, K$ and
  every $P in cal(M)$.
== Rewriting the efficient influence function
    The Gateaux derivative is then given by
    $
        phi_tau^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1)))   \
            & times bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} ((macron(Z)^a_(k,tau) (tau)- Qbar(k-1) (tau)) \
                &quad + integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1) (tau)-Qbar(k-1) (u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u))\
            & +  Qbar(0) (tau) - Psi_tau^g (P),
    $


== Practical considerations
- We consider a one-step estimator based on the EIF.
#pause
- Simulation studies demonstrate favorable performance of the proposed procedure -- lower bias than discrete-time procedures
  and good coverage of confidence intervals.
- However, variance estimation is challenging due to the censoring martingale term.

== Perspectives
- Estimating the martingale term
    - Undersmoothing of the estimation of the censoring compensator to avoid estimation altogether.
    - Using a machine learning methods that can handle multivariate outcomes.
#pause
- Using a TMLE approach instead of one-step approach $=>$ better because we want estimates in $[0, 1]$.
#pause
- Identifiability, i.e., does the target parameter have a causal interpretation? 
#pause
- Similar ideas for other target parameters, e.g., recurrent events, restricted mean survival time, etc.

= Appendix 
#bibliography("references/ref.bib",style: "apa")
