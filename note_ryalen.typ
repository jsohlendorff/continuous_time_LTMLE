#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion
#import "@preview/ctheorems:1.1.3": 
#set footnote(numbering: "*")

#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#import "@preview/numty:0.0.5" as nt
#set cite(form: "prose")
// Color references red
#show  ref: it => {text(fill: maroon)[#it]}

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof")
#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)
#set math.equation(numbering: "(1)")
#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("")
  ] else {
    it
  }  
}

#show: thmrules.with(qed-symbol: $square$)
#set heading(numbering: "1.a)")

// In discrete time, the two formula are the same because every discrete time is a visitation event?
// What if we are still in discrete time, but the treatment decision is not made at every time point, but randomly; then it maybe does not relate to discrete time theories
// It appears then that the formulas can still be different. 

= A causal interpretation in terms of potential outcomes of target parameter in @rytgaardContinuoustimeTargetedMinimum2022

We consider a setting similar to the one of @ryalenPotentialOutcomes
and @rytgaardContinuoustimeTargetedMinimum2022.
As in @rytgaardContinuoustimeTargetedMinimum2022,
we consider some measure $P$ on a probability space
$(Omega, cal(F), P)$.
We consider a setting in which we observe a
multivariate random measure $N = (N^y, N^a, N^ell)$
which is defined on $(Omega, cal(F))$,
where any two of the components do not jump at the same time.
These processes are observed in
$[0, T]$ for some $T > 0$.
Here, $N^y$ denotes an outcome process of interest $Y$ (e.g., death),
random measure $N^a$
on $[0, T] times cal(A)$ for treatment $A$,
where $cal(A)$ is a measurable space;x
$N^ell$ denotes a random measure for covariates $L$
on $[0, T] times cal(L)$,
where $cal(A)$ and $cal(L)$ are measurable spaces;
for instance finite subsets of $RR$ and $RR^d$.
Such a random measure gives rise to a filtration
$(cal(F)_t)_(t >= 0)$,
where
$
    cal(F)_t := sigma(N^y (dif s), N^a (dif s times {x}), N^ell (dif s times {y}) | s in (0, t], x in cal(A), y in cal(L)).
$
Further, we make the assumption of no explosion of $N$.

We concern ourselves with the hypothetical question
if the treatment process $N^a$ had been
intervened upon such that treatment was given according to some
treatment regime $g^*$.
We will work with an intervention
that specifies the treatment decisions
but does not change timing of treatment visits.
What this means precisely will be made clear below.
We are interested in the outcome process $Y$ under this intervention,
which we denote by $tilde(Y)$.
Importantly, the intervention is defined as a static/dynamic intervention
$
    N^(g^*) (dif t times dif x) = pi^*_t (dif x) N^a (dif t times cal(A))
$
where $pi^*_t (dif x)$ is some kernel
that specifies the treatment decision deterministically at time $t$
in the sense that there are functions $g^*_k : bb(H)_(k-1) times [0, T] -> cal(A)$
such that
$
    pi^*_t (dif x) = sum_k bb(1) {event(k-1) < t <= event(k)} delta_(g^*_k (history(k-1), event(k))) (dif x),
$
i.e., $g_k^*$ is $history(k-1) times.circle cal(B) ([0, T])$-measurable
This means that, critically,
$N^(g^*) (dif t times dif x)$ is also a random measure.
Note that $N^(g^*)$ has the compensator
$
    scr(L) (N) (dif t times dif x) = pi^*_t (dif x) underbrace(Lambda^a (dif t times cal(A)), =:Lambda^a (dif t)),
$
where $Lambda^a (dif t)$ is the $P$-$cal(F)_t$-compensator of $N^a (dif t times cal(A))$.
However, $N^a$ generally has the compensator $Lambda^(a) (dif t times dif x) = pi_t (dif x) Lambda^a (dif t)$.
Now define the time to deviation from the treatment regime as
$
    tau^(g^*) = inf {t >= 0 | N^a ((0, t] times {x}) != N^(g^*) ((0, t] times {x}) " for some " x in cal(A)},
$
when $cal(A) = {a_1, dots, a_k}$ consists of a finite set of treatment options.

#definition[
    A multivariate random measure $tilde(N) = (tilde(N)^y, tilde(N)^a, tilde(N)^ell)$
    is a *counterfactual random measure* under the intervention $g^*$
    if it satisfies the following conditions.
    Let $cal(tilde(F))_t := sigma(tilde(N)^y (dif s), tilde(N)^a (dif s times {x}), tilde(N)^ell (dif s times {y}) | s in (0, t], x in cal(A), y in cal(L))$.
    Let $scr(L)$ denote the $P$-$cal(F)_t$-canonical compensator of $N^(g^*)$
    and let $Lambda$ denote the $P$-$cal(F)_t$-compensator of $N$.
    1. $tilde(N)^a$ has compensator $scr(L) (tilde(N))$ with respect to $cal(tilde(F))_t$.
    2. $tilde(N)^x$, has the same compensator $Lambda (tilde(N))$ with respect to $cal(tilde(F))_t$ for $x in {y, ell}$.
]

The main outcome of interest is the counterfactual outcome process
$tilde(Y) := tilde(N)^y$;
and we wish to identify $mean(P) [tilde(Y)_t]$.

//It has been discussed in discrete time (@RobinsLongitudinal2001)
//that the g-formula is unique; however, as we shall
//see the g-formula in continuous time may not necessarily be uniquely defined.
//Specifically this may relate to conditional distributions
//in this setting not being uniquely defined.
// We are interested in the counterfactual mean outcome $mean(P) [tilde(Y)_t]$,
// where $(tilde(Y)_t)_(t >= 0)$ is the counterfactual outcome process
// of $Y := N^y$ under the intervention that sets treatment to $1$ at all visitation times.
// Note the different exchangeability condition compared to @ryalenPotentialOutcomes,
// as @ryalenPotentialOutcomes expresses exchangeability through the counting process $bb(1) {tau^(g^*) <= dot}$.
//this appears to me to be a weaker condition (?).

Let $(event(k), status(k), treat(k))$
denote the ordered event times, event types, and treatment decisions at event $k$.
Note that @eq:rytgaard is the same likelihood ratio as in @rytgaardContinuoustimeTargetedMinimum2022.
As a shorthand, we let $N^(a, x) (dif t) := N^a (dif t times {x})$ for $x in cal(A)$.
//We also assume that we work with a version of the compensator
//such that $Lambda ({t} times {y, a} times {1, 0}) < oo$ for all $t > 0$.
//We may generally also work with a compensator $Lambda$ that fulfills conditions (10.1.11)-(10.1.13) of @last1995marked.
// Let $pi_(event(k)) (history(k-1))$ denote the treatment probability
// and let $pi^*_(event(k)) (history(k-1))$ denote the treatment probability under the intervention $g^*$


// *NOTES:*
// - Does the exchangeability condition simplify in the case of $cal(n)^a$ predictable in $P$-$cal(F)_t$
//   as specified in @ryalenPotentialOutcomes; as noted in their article the two likelihood ratios
//   turn out two be the same in the case of orthogonal martingales.

//   Suppose that $cal(n)^a$ is predictable
//   so that $N^(a 1) (dif t)$ is predictable
//   in that case the first exchangeability condition is trivial;
//   Pål's condition only grants exchangeability for
//   $N^(a 1) (t and tau^(g^*)) $ is predictable;
//   I think that this is the sufficient for the argument to go through. 

// - Positivity holds for example if $pi_t$ is bounded away from $0$ and $1$
//   and $N_t$ has bounded number of jumps in the study period. 

// UI (Uniform integrability) implies zeta (t) = integral ... is uniformly integrable martingale,
// but why is integral_0^t tilde(Y)_(t) zeta (dif s) a martingale (generally a martingale)

// If there are two solutions (mine and theirs), they may be an infinite number of solutions
// due to convexity
//

// Necessary criteria for the conclusion to hold
// for two measures Q in terms of P
// 1. E_P [tilde(Y)_t] = E_Q [Y_t]
// 2. Q(tau^(g^*) > t) = 1
// 3. Q and P are equivalent on cal(F)_t and the likelihood ratio is W(t)

// Look for restrictions on such that positivity in one situation implies the other
// It is natural to ask what the differences between the EIF in mine and Pål's paper are
// and whether the variance of one is smaller than the other?

// E_P[tilde(W)_t Y_t] = E_P[W_t Y_t]; can this hold? yes if E_P[tilde(W)_t | Y_t, W_t] = 1?
// Pål assumes that exchangeability holds for the weights; therefore E[tilde(Y)_t W_t] = E[tilde(Y)_t W_0]
// by conditioning.
// CAR is stronger than exchangeability => likelihood factorizes, but we do not need it to. 
#theorem[
If _all_ of the following conditions hold:
- *Consistency*: $tilde(Y)_(dot) bb(1) {tau^(g^*) > dot} = Y_(dot) bb(1) {tau^(g^*) > dot} quad P-"a.s."$
- *Exchangeability*:
  Define $cal(H)_t := cal(F)_t or sigma(tilde(Y))$.
  //The $P$-$cal(F)_t$ compensator for $N^a$ is also the $P$-$cal(H)_t$ compensator.
  //The $P$-$cal(H)_t$ Radon-Nikodym derivative of the compensator of $N^a$ with respect to the total $P$-$cal(H)_t$ compensator given by
  //$pi_t (dif x)$ is $cal(F)_t$-measurable.
  The Radon-Nikodym derivative of the $P$-$cal(F)_t$ compensator with respect to the total $P$-$cal(H)_t$ compensator is the same as the Radon-Nikodym derivative of the $P$-$cal(F)_t$ compensator with respect to the total $P$-$cal(F)_t$ compensator.
  
- *Positivity*: 
  $
      W (t) := product_(j = 1)^(N_t) (product_(i=1)^(k) ((pi^*_(event(j)) ({a_i}; history(j-1))) / (pi_(event(j)) ({a_i}; history(j-1))))^(bb(1) {treat(k) = a_i}))^(bb(1) {status(j) = a}) 
  $ <eq:rytgaard>
  is a uniformly integrable $P$-$cal(F)_t$-martingale.
  
  Furthermore, assume that $K(t) = integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s)$
  is a $P$-$cal(F)_t$-martingale and that $K$ is a process of *locally integrable variation*, meaning that $mean(P) [integral_0^t |d K(s)| ] < oo$ for all $t > 0$.

Then,
$
    mean(P) [tilde(Y)_t] = mean(P) [Y_t W (t)]
$
    and $W (t) = cal(E) (K)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale, where $cal(E)$ denotes the Doléans-Dade exponential (@protter2005stochastic).
] <thm:identifiabilitymartingale>

#proof[
    We shall use that the likelihood ratio solves a specific stochastic differential equation.
    To this end, note that
    $
        W(t) &= cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s))_t \
            &=^((*)) cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) - sum_(j=1)^(k) (pi_s^* ({a_j}) - pi_s ({a_j})) Lambda^(a) (dif s))_t \
            &= cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) - sum_(j=1)^(k) ((pi_s^* ({a_j})) / (pi_s ({a_j})) - 1) Lambda^(a, a_j) (dif s))_t \
            &= cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s))_t.
    $
    In $(*)$, we use that $sum_(j=1)^k pi_s ({a_j}) = sum_(j=1)^k pi_s^* ({a_j}) = 1$.
        
    Thus, by properties of the product integral (e.g., Theorem II.6.1 of @andersenStatisticalModelsBased1993),
    $
        W(t) = 1 + integral_0^t W(s -) sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s).
    $ <eq:sde>
    We have that
    $
        zeta_t := integral_0^t W(s -) sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s)
    $ is a zero mean $P$-$cal(H)_t$-martingale by positivity.
    From this, we see that $integral_0^t tilde(Y)_(t) zeta (dif s)$ is also a uniformly integrable $P$-$cal(H)_t$-martingale
    by Theorem 2.1.42 of @last1995marked.
    This implies that
    $
        mean(P) [Y_t W (t)] &=^((**)) mean(P) [tilde(Y)_t W (t)] = mean(P) [tilde(Y)_t mean(P) [W(t) | cal(H)_0]]= mean(P) [tilde(Y)_t W (0)] = mean(P) [tilde(Y)_t] 
    $
    where in $(**)$ we used consistency by noting that $W (t) != 0$ if and only if $tau^(g^*) > t$.
]

Note that in the proof, it suffices that $W(t)$ is uniformly bounded because
then it will also be a $P$-$cal(H)_t$-martingale
since it is a local, bounded $P$-$cal(H)_t$-martingale.

It is also natural to ask oneself: how does
our conditions
relate to the ones of @ryalenPotentialOutcomes?
The condition of consistency is the same.
However, the exchangeability condition and
the positivity condition are different in general.
We present slightly strengthened versions of the conditions
as these are easier to compare.
Let $bb(N)_t^a = bb(1) {tau^(g^*) <= t}$
and let $bb(L)_t$ denote its $P$-$cal(F)_t$-compensator.

- *Exchangeability*: 
  Define $cal(H)_t := cal(F)_t or sigma(tilde(Y))$.
  The $P$-$cal(F)_t$ compensator for $bb(N)^a$ is also the $P$-$cal(H)_t$ compensator.

- *Positivity*:
  $
      tilde(W) (t) := (cal(E) (-bb(N)^a))_t / (cal(E) (-bb(L)^a))_t = cal(E) (tilde(K))_t
  $
  is uniformly integrable, where $tilde(K)_t = integral_0^t 1/(1- Delta bb(L)^a_s ) (bb(N)^a (dif s) - bb(L)^a (dif s))$.
  Furthermore, $tilde(K)$ is a process of *locally integrable variation*
  and a $P$-$cal(F)_t$-martingale.

== Comparison with the exchangeability condition of @ryalenPotentialOutcomes

#theorem[
    Let $bb(N)_t^a = bb(1) {tau^(g^*) <= t}$.
    The exchangeability condition of @thm:identifiabilitymartingale implies the one of @ryalenPotentialOutcomes, e.g.,
    $bb(L)_t$ is both the $P$-$cal(F)_(t)$ compensator 
    and the $P$-$cal(H)_(t)$ compensator of $bb(N)_t^a$.
]

#proof[
  First, let 
//  A deterministic treatment regime is given by some measurable
//    functions $g^*_k : bb(H)_(k) times [0, T] -> cal(A)$ so that 
  $
      N^(a,*) (dif t) =  sum_k sum_j bb(1) {event(k-1) < t <= event(k)}  bb(1) {j != g^*_k (history(k-1), t)}  N^(a, a_j) (dif t),
  $
  which is the counting measure for the number of deviations from the treatment regime $g^*$ and consider
  $
      bb(1) (t <= event(K)) N^(a,*) (dif t) =sum_(k=1)^K sum_j bb(1) {event(k-1) < t <= event(k)}  bb(1) {j != g^*_k (history(k-1), t)}  N^(a, a_j) (dif t),
  $
  for some $K$.
  Note that $(bb(1) {tau^(g^*) <= t} N^(a,*) (dif t))^p = bb(1) {tau^(g^*) <= t} Lambda^(a,*) (dif t)$,
  where $p$ denotes the predictable projection (@last1995marked),
  by definition of the predictable projection. On the other hand,
  $
      &(sum_(k=1)^K sum_j bb(1) {event(k-1) < t <= event(k)} bb(1) {j != g^*_k (history(k-1), t)}  N^(a, a_j) (dif t))^p \
          &= sum_(k=1)^K sum_j (bb(1) {event(k-1) < t <= event(k)} bb(1) {j != g^*_k (history(k-1), t)}  N^(a, a_j) (dif t))^p \
          &=^((*)) sum_(k=1)^K sum_j bb(1) {event(k-1) < t <= event(k)} bb(1) {j != g^*_k (history(k-1), t)} (N^(a, a_j) (dif t))^p \
          &= sum_(k=1)^K sum_j bb(1) {event(k-1) < t <= event(k)} bb(1) {j != g^*_k (history(k-1), t)} Lambda^(a, a_j) (dif t),
  $ <eq:pred_proj>
  where we use in $(*)$ that $bb(1) {event(k-1) < t <= event(k)}  bb(1) {j != g^*_k (history(k-1), t)}$ is predictable (Theorem 2.2.22 of @last1995marked).
  Letting $K -> oo$ and using the assumption of no explosion
  shows that the $P$-$cal(F)_t$-compensator of $N^(a,*) (dif t)$ is
  given by the limit as $K -> oo$ of the right-hand side of @eq:pred_proj.
  Since $bb(N)_t^a = N^(a,*) ((0, t and tau^(g^*)])$, the corollary on p. 10 of @protter2005stochastic,
  implies that the $P$-$cal(F)_t$-compensator of $bb(N)^a_t$ is
  $
      bb(L)^a_(t) = sum_k sum_j bb(1) {event(k-1) < t <= event(k)} bb(1) {j != g^*_k (history(k-1), t)} Lambda^(a, a_j) (t and tau^(g^*)).
  $
  by using the limit of the right-hand side of @eq:pred_proj.
  If exchangeability holds (given in
  @thm:identifiabilitymartingale),
    then the same argument applies with $cal(H)_t$ instead of $cal(F)_t$.
  This is the desired result.
]

== Comparisons of the positivity assumptions in @ryalenPotentialOutcomes

One may ask oneself if positivity holds in @ryalenPotentialOutcomes;
under what assumptions does positivity in @thm:identifiabilitymartingale
hold? In general, however, it would appear that the two positivity conditions
are different and neither implies the other.

Can we find a process $phi$ such that
$cal(E) (K) =  (cal(E) (-bb(N)^a)) / (cal(E) (-bb(L)^a)) cal(E) (phi)$?

#theorem[
    $phi$ is given by
        $
            phi_t = K_t - bb(L)_t^a + bb(N)_t^a - [K, bb(L)^a]_t,
        $
    where $[dot, dot]$ denotes the quadratic covariation process (@protter2005stochastic),
    where
    $
        [K, bb(L)^a]_t &= integral_0^(t and tau^(g^*)) sum_v bb(1) {event(v-1) < s <= event(v)} sum_(i != g^*_v (history(v-1), event(v))) pi_s ({a_j}) Delta Lambda^(a) (s) \
            &qquad times sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) \
    $
    In the absolutely continuous case, $[K, bb(L)^a]_t = 0$ as $Delta Lambda^a_t = 0$ for all $t > 0$.
    If, further, $pi_t^* ({a_j}) = 1$ for some $j$,
    then
    $
        phi_t = integral_0^(t and tau^(g^*)) ((1)/(pi_s) - 1) M^(a, a_j) (dif s).
    $
]
#proof[
    To this end, let $v := bb(1) {W(t) > 0, tilde(W) (t) > 0} = bb(1) {tau^(g^*) > t} = cal(E) (- bb(N)^a)$
    and calculate 
$
    cal(E) (phi) v &= (cal(E) (K) cal(E) (- bb(L)^a)) / (cal(E) (- bb(N)^a)) v \
        &= cal(E) (K) cal(E) (-bb(L)^a) v \
        &= cal(E) (K - bb(L)^a - [K, bb(L)^a]) v \
        &= cal(E) (K - bb(L)^a + bb(N)^a - [K, bb(L)^a]) v,
$
where the last equality follows since $bb(N)^a v equiv 0$.
Note that
$
    [K, bb(L)^a]_t &= integral_0^t Delta bb(L)^a_s sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) \
        &=^(*) integral_0^(t and tau^(g^*)) sum_v bb(1) {event(v-1) < s <= event(v)} sum_(i != g^*_v (history(v-1), event(v))) pi_s ({a_j}) Delta Lambda^(a) (s) \
            &qquad times sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) 
$

In the case where $Delta Lambda^a_s equiv 0$ and $pi_s^* ({a_j}) = 1$ for some $j$,
then

$
    v(K_t - bb(L)_t^a + bb(N)_t^a) = v integral_0^(t and tau^(g^*)) ((1)/(pi_s) - 1) M^(a, a_j) (dif s)
$
and $[K, bb(L)^a]_t = 0$.
]

A simple consequence of this is the following.
Assume that $Q_"ryalen" << P$ with $Q_"ryalen" = (cal(E) (-bb(N)^a)) / (cal(E) (-bb(L)^a)) bullet P$.
and, say, $cal(E) (phi)$ is a uniformly integrable $Q_"ryalen"$-$cal(F)_t$-martingale,
i.e., that $Q << Q_"ryalen"$, then $Q_"ryalen" << P$ implies that $Q << P$.
This happens for example if $cal(E) (phi)$ is uniformly bounded by a constant.

= Comparison with the @rytgaardContinuoustimeTargetedMinimum2022

In @rytgaardContinuoustimeTargetedMinimum2022,
both an exchangeability condition and a
positivity condition are presented,
but no proof is given that these conditions
imply that their target parameter is identified.
Our proposal shows that under the conditions of @thm:identifiabilitymartingale,
the g-formula given in @rytgaardContinuoustimeTargetedMinimum2022
causally identifies the counterfactual mean outcome
under the assumption that the other martingales are orthogonal
to the treatment martingale.
Lemma 1 of @ryalenPotentialOutcomes then gives the desired target parameter.
Note that this is slightly weaker than @rytgaardContinuoustimeTargetedMinimum2022,
as they implicitly require that _all_ martingales are orthogonal
due to their factorization of the likelihood. This is because
$cal(E) (X) cal(E) (Y) = cal(E) (X + Y)$ if and only if $[X, Y] = 0$.
This can be seen by applying Theorem 38, p. 130 of @protter2005stochastic
and using that the stochastic exponential solves a specific stochastic differential equation.

//A lingering question is whether the desired $g$-formula
//can be obtained even if the martingales are not orthogonal.
#theorem("g-formula")[
    Let $Lambda_P^a (dif t)$ denote the total $P$-$cal(F)_t$-compensator of $N^a$.
    Furthermore, let $Lambda_P^x$ denote the $P$-$cal(F)_t$-compensator of $N^x$ for $x in {y, ell}$.
    Under positivity, then
    1. The $Q$-$cal(F)_t$ compensator of $N^a (dif t times dif x)$ is $pi^*_t (dif x) Lambda_P^a (dif t)$.
    2. The $Q$-$cal(F)_t$ compensator of $N^x$ is $Lambda_P^x$ for $x in {y, ell}$ // addition should be zero; by Jacods formula for likelihood ratios
]

#proof[
    First note that for a local $cal(F)_t$-martingale $X$ in $P$, we have
    $
        integral_0^t 1/(W_(s -)) dif angle.l W, X angle.r_s^P = angle.l K, X angle.r_t^P
    $ <eq:girsanov1>
    since we have that $W_t = 1 + integral_0^t W_(s -) dif K_s$; whence
    $
        angle.l W, X angle.r_t = angle.l 1, X angle.r_t + angle.l W_(-) bullet K, X angle.r_t = W_(t -) bullet angle.l K, X angle.r_t
    $ 
    With $X= M^(a, x)$, we find
    $
        angle.l K, M^(a, x) angle.r_t^P &= integral_0^t sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif angle.l M_P^(a, a_j), M_P^(a, x) angle.r_s^P \
            &= integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) dif angle.l M_P^(a, x) angle.r_s^P \
            &quad + sum_(j != x) integral_0^t ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif angle.l M_P^(a, a_j), M_P^(a, x) angle.r_s^P \
            &= integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) pi_s (x) Lambda_P^a (dif s) \
            &quad - integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) Delta (pi (x) Lambda_P^a)_s pi_s (x) Lambda_P^a (dif s) \
            &quad - sum_(j!= x) integral_0^t ((pi_s^* (a_j))/(pi_s (a_j)) - 1) Delta (pi (x) Lambda_P^a)_s pi_s (a_j) Lambda_P^a (dif s) \
            &= integral_0^t (pi_s^* (x) - pi_s (x)) Lambda_P^a (dif s) \
            &quad - sum_(j) integral_0^t (pi_s^* (a_j) - pi_s (a_j)) Delta (pi (x) Lambda_P^a)_s Lambda_P^a (dif s) \
            &= integral_0^t (pi_s^* (x) - pi_s (x)) Lambda_P^a (dif s).
    $ <eq:girsanova>
    Girsanov's theorem (Theorem 41, p. 136 of @protter2005stochastic)
    together with @eq:girsanov1 and @eq:girsanova
    gives that 
    $
        N^a (dif t times dif x) - pi_t (dif x) Lambda_P^a (dif t) - (pi_t^* (dif x) - pi_t (dif x)) Lambda_P^a (dif t) = N^a (dif t times dif x) - pi_t^* (dif x) Lambda_P^a (dif t)
    $
    is a $Q$-$cal(F)_t$-local martingale. The second statement follows by noting that
    $
        [M^(y), K]_t &= integral_0^t Delta N_t^y sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) N^(a, a_j) (dif s)  \
            &- integral_0^t Delta Lambda_P^y (s) sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) M^(a, a_j) (dif s) \
    $
    where we apply the trick with adding and subtracting the treatment compensators in the second term.
    The first term is zero because no two counting processes jump at the same time.
    The second term is a local martingale. This implies $angle.l M^(y), K angle.r_t^P = 0$.
    For $x=ell$ the argument is the same.
]

== Comparison of the exchangeability condition of @rytgaardContinuoustimeTargetedMinimum2022
Additionally, consistency is not explicitly stated,
so we cannot compare this condition.
The stated positivity condition is the same as the one in @thm:identifiabilitymartingale,
so left is to compare the exchangeability conditions.

We can also ask ourselves:
Is the exchangeability criterion in @thm:identifiabilitymartingale
close in interpretation 
to the statement of @rytgaardContinuoustimeTargetedMinimum2022?
In @rytgaardContinuoustimeTargetedMinimum2022,
the statement is:
$
    (tilde(Y)_t)_(t in [0, T]) perp A(T_(k)^a) | cal(F)^(-)_(T_(k)^a), qquad (\')
$ for all $k$, where $T_(k)^a$ are the ordered treatment event times, where $cal(F)^(-)_(T)$ is defined on p. 62 of @last1995marked.
This $sigma$-algebra contains all the information that occurs strictly before time $T$.

In this case, we can express one condition (in addition to another) for our exchangeability
as something that is very similar (@thm:exchangeabilityequivalence),
$
    (tilde(Y)_t)_(t in [0, T]) perp treat(k) | Delta N_(event(k))^a = 1, event(k), history(k-1), qquad (\*)
$ 
for all $k$. A slightly weaker statement than $(\*)$ is that
- The Radon-Nikodym derivative of $Lambda^(a, a_j) (dif t)$ with respect to $Lambda^a (dif t)$
  is the same for $cal(F)_t$ and $cal(H)_t$. (\*!)
// This is because there is a version of $pi_t$ such that
// $
//     pi_t^' = sum_k bb(1) {event(k-1) < t < event(k)} pi_(event(k)) (cal(H)_(event(k-1)))
// $

The statements $(')$ and $(*)$ appear similar, but are generally not the same,
since $S$ and $Delta N_S^a$ are not generally $cal(F)_T^-$ measurable
for a stopping time $S$.

Let $S = T_(k)^a$ for some $k$.
If $S$ and $Delta N_S^a$ are $cal(F)_S^-$ measurable, then whenever $(')$ holds, we have 
$
    (tilde(Y)_t)_(t in [0, T]) perp A(T_(k)^a) | T_k^a, Delta N_(T_k^a)^a, cal(F)^(-)_(T_(k)^a)
$
which implies $(\*)$.

If $N^a (dot times {0,1})$ is a predictable counting process
with respect to $cal(F)_t$, we will see that this indeed is the case.
If this holds, $S$ is predictable, and so $S in sigma(cal(F)_S^-)$ (Theorem 2.2.19 of @last1995marked).
If $N^a_t$-predictable, then $N_t^a in sigma(cal(F)_(t-), t)$ (Theorem 2.2.6 of @last1995marked);
therefore $Delta N_S^a in sigma(cal(F)_S^-, S)$.
//However, due to the classical fact that conditional independence and independence
//never imply each other, the two statements are not equivalent and are generally different.
// If it does not depend on T_a, is that enough?

To have exchangeability in the sense of @thm:exchangeabilityequivalence, we also need that the compensator for $N^a = N^a (dot times {0,1})$ is the same under $cal(F)_t$ and $cal(H)_t$,
i.e., that
- $Lambda^a (dif t)$ is the $P$-$cal(F)_t$-compensator and the $P$-$cal(H)_t$-compensator of $N^a (dif t times {0,1})$. (\*\*)
This is obviously the case if $N^a (dot times cal(A))$ is $cal(F)_t$-predictable.

We then have the following result.
#theorem[
    The conditions (\*\!) and (\*\*) hold if and only if the exchangeability condition of @thm:identifiabilitymartingale holds.
] <thm:exchangeabilityequivalence>

#proof[
    Obvious.
// To see that it is sufficient, note that (\*) and (\*\*) imply that
//     $
//         N^a (dif t times {x}) - (pi_t)^(bb(1) {x=1}) (1-pi_t)^(bb(1) {x=0}) Lambda^a (dif t)
//     $ <eq:1>

    //in view of (\*).
    // Furthermore, a version of $Lambda^a (dif t)$ is
    // $
    //     Lambda^(a ') (dif t) = sum_(k) bb(1) {event(k-1) < t < event(k)} Lambda_k^a (dif t | cal(H)_(event(k-1)))
    // $
    //which must be both the $P$-$cal(F)_t$-compensator and the $P$-$cal(H)_t$-compensator of $N^a (dif t times {0,1})$ by (\*\*).
    //By Theorem 4.1.11 of @last1995marked, @eq:1 is a $P$-$cal(H)_t$ - local martingale.
    // However, it must also be a $P$-$cal(F)_t$-local martingale;
    // to see this, let $S_n$ be a localizing sequence for $M_(t)^(a x)$ and consider $0 <= s < t$.
    // Then,
    // $
    //     mean(P) [M_(t and S_n)^(a x) | cal(F)_s] &= mean(P) [mean(P) [M_(t and S_n)^(a x)| cal(H)_s]  | cal(F)_s] \
    //         &= mean(P) [M_(s and S_n)^(a x) | cal(F)_s] =^(!) M_(s and S_n)^(a x) quad P-"a.s.".
    // $
    // In $!$, we used that $N_(s and S_n)^(a x)$ is (trivially) $cal(F)_s$ measurable;
    // moreover, by (\*), $pi_s$ is $cal(F)_s$ measurable;
    // finally, by (\*\*), $Lambda^(a) (dif t)$ is also the $P$-$cal(F)_t$-compensator of $N^a (dif t times {0,1})$;
    // and hence it is predictable with respect to this filtration because it is $cal(F)_(t-)$ measurable (Theorem 2.2.6 of @last1995marked).
    // // Nulmængder???? If we complete the filtration, then this argument should be ok.
    // Conversely, to see that it is necessary, we have directly (\*\*); however this is precisely what we needed to show $(\*!)$.
]

= Which other solutions can we think of besides the one given in @thm:identifiabilitymartingale and in @ryalenPotentialOutcomes?

#theorem[
    Let $K^*_t$ be a (local) martingale with $Delta K_t^* >= -1$
    and $Delta K_t^* > -1$ if $t < tau^(g^*)$. Then, 
$
    W_t^* := cal(E) (K^*)_t = cal(E) (K^*)_t cal(E) (- bb(N)^a)_t quad P-"a.s."
$
    if and only if
$
    bb(1) {tau^(g^*) < oo} K^*_(tau^(g^*)) = - bb(1) {tau^(g^*) < oo} quad P-"a.s."
$
]
#proof[
    Using the well-known formula $cal(E) (X) cal(E) (Y) = cal(E) (X + Y + [X, Y])$,
    we have
    $
        cal(E) (K^*) = cal(E) (K^* - bb(N)^a - [K^*, bb(N)^a])
    $
    This holds if and only if
    $
        1 + integral_0^t W_(t -) dif K^*_s = 1 + integral_0^t W_(t -) dif (K^*_s - bb(N)^a_s - [K^*, bb(N)^a]_s)
    $
    if and only if
    $
        integral_0^t W_(t -) Delta K_s^* dif bb(N)^a_s = - integral_0^t W_(t -) dif bb(N)^a_s 
    $
    and this is
    $
        bb(1) {tau^(g^*) <= t} W_(tau^(g^*) -) Delta K_(tau^(g^*)) = - bb(1) {tau^(g^*) <= t} W_(tau^(g^*) -)
    $
    By assumption, $W_(tau^(g^*) -) > 0$ (looking at the explicit solution of the SDE) and so the above holds if and only if
    $
        bb(1) {tau^(g^*) <= t} Delta K_(tau^(g^*)) = - bb(1) {tau^(g^*) <= t}
    $
    Taking $t -> oo$ gives the desired result. On the other hand, if the result holds then,
    $
        bb(1) {tau^(g^*) <= t} Delta K_(tau^(g^*)) &= bb(1) {tau^(g^*) <= t} bb(1) {tau^(g^*) < oo} Delta K_(tau^(g^*)) \
            &=bb(1) {tau^(g^*) <= t} bb(1) {tau^(g^*) < oo} (-1) = - bb(1) {tau^(g^*) <= t}
    $
] 

Now, we consider only $K^*$'s of the form 
$
    K^* (t) = integral sum_(x in cal(A)) bb(1) {s <= t} tilde(h) (s, x) M^(a, x) (dif s)
$
with $tilde(h) (s, x)$ $P$-$cal(F)_t$ predictable
with the restriction stated in the above theorem.
//We also suppose that $Delta Lambda^(a, x)_t < 1$.
//This happens for example if $Delta Lambda^a_t < 1$.
The above theorem gives that we must have
$
    Delta K^*_(tau^(g^*)) = sum_(x in cal(A)) tilde(h) (tau^(g^*), x) Delta M^(a, x)_(tau^(g^*)) = -1
$
on the event that $tau^(g^*) < oo$.
Suppose that $cal(A) = {a_0, a_1}$
and that $pi_t^* (a_1) = 1$.
In this case, we can write the equation above as
$
    h(tau^(g^*), a_1) (0 - pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*))) + h(tau^(g^*), a_0) (1 - (1- pi_(tau^(g^*)) (a_1)) Delta Lambda^(a)_(tau^(g^*))) = -1
$
or
$
    (h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*)) + h(tau^(g^*), a_0) (1 - Delta Lambda^(a)_(tau^(g^*))) = -1
$
We consider various cases:
- Absolutely continuous case: $Delta Lambda^(a) equiv 0$.
- $macron(N)^a$ is $cal(F)_t$-predictable.
- Jump times for $macron(N)^a$ are discrete.
- General case.

== Absolutely continuous case <sec:absolutely_continuous_case>
In this case, conclude that $h(tau^(g^*), a_0) = -1$.
However, nothing else can be said about $h(tau^(g^*), a_1)$
as the equation does not place any other restrictions than
it being predictable.
We can, however, conclude that $integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) = integral_0^(t and tau^(g^*)) (-1) M^(a, a_0) (dif s) = - bb(N)^(a) (t) + bb(L)^(a) (t)$
whenever that integral happens to be of finite variation.
To see this, note that
$
    integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) &= integral_0^(t and tau^(g^*)) h(s, a_0) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) h(s, a_0) Lambda^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (-1) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) h(s, a_0) Lambda^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (-1) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_0) + 1) Lambda^(a, a_0) (dif s),
$
meaning that $integral_0^(t and tau^(g^*)) (h(s, a_0) + 1) Lambda^(a, a_0) (dif s)$
is of finite variation, a local martingale, predicable and hence constant (and thus zero)
by Theorem 15, p. 115 of @protter2005stochastic.

== $macron(N)^a$ is $cal(F)_t$-predictable
Im this case, $Delta Lambda_t^a = Delta macron(N)_t^a$
which is 1 at $t = tau^(g^*)$.
Therefore,
$
    (h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) = -1
$
or
$
    h(tau^(g^*), a_0) = h(tau^(g^*), a_1) - 1/(pi_(tau^(g^*)) (a_1))
$
Thus, we have
$
    K^(h)_t &= integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) + integral_0^(t and tau^(g^*)) h(s, a_1) M^(a, a_1) (dif s) \
        &= integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_1)) M^(a, a_0) (dif s) + integral_0^(t and tau^(g^*)) (h(s, a_1)) M^(a) (dif s) \
        &= integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) Lambda^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) ((h(s, a_0)-h(s, a_1)) + 1/(pi_(s) (a_1))) Lambda^(a, a_0) (dif s) \
$
Assuming that $integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s)$ is of finite variation,
we have that $integral_0^(t and tau^(g^*)) ((h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s) = integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) M^(a, a_0) (dif s)$.
We conclude that $K^(h)_t$ if $integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s)$ is of finite variation
does not depend on the choice of $h$.
Therefore, the stochastic exponential $cal(E) (K^(h))_t$ does not depend on the choice of $h$ either,
and we may conclude that $cal(E) (K^(h))_t = cal(E) (K)_t$.

== General case
Suppose that $(1-pi_t (a_1)) Delta Lambda^(a)_(t) < 1$ for all $t > 0$.
Otherwise, an argument similar to the one we will give will split into cases.

We have that
$
    &(h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) Lambda^(a) ({tau^(g^*)}) bb(1) {Lambda^(a) ({tau^(g^*)}) > 0} \
        &quad + h(tau^(g^*), a_0) (1 - Lambda^(a) ({tau^(g^*)})) bb(1) {Lambda^(a) ({tau^(g^*)}) > 0} \
        &quad + h(tau^(g^*), a_0) (bb(1) {Lambda^(a) ({tau^(g^*)}) = 0}) = -1
$

By the same argument as in the absolutely continuous case,
we have that
$
    &integral_0^(t and tau^(g^*)) h(s, a_0) bb(1) {Lambda^(a) ({s}) = 0} M^(a, a_0) (dif s) \
        &= - integral_0^(t and tau^(g^*)) bb(1) {Lambda^(a) ({s}) = 0} M^(a,a_0) (dif s) \
        &= - bb(N)^(a) (t) bb(1) {Lambda^(a) ({tau^(g^*)}) = 0} + bb(L)^(a, c) (t),
$
where $bb(L)^(a, c)$ is the continuous part of $bb(L)^a$.
Next whenever $Lambda^(a) ({tau^(g^*)}) > 0$, we find
$
    h(tau^(g^*), a_0) = (- 1 + h(tau^(g^*), a_1) pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*))) / (1 - (1-pi_(tau^(g^*)) (a_1)) Delta Lambda^(a)_(tau^(g^*)))
$
Therefore, it will again be the case that
$
    &integral_0^(t and tau^(g^*)) h(s, a_0) bb(1) {Lambda^(a) ({s}) > 0} M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1 + h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1 - (1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) bb(1) {Lambda^(a) ({s}) > 0} M^(a, a_0) (dif s) \
$
Conclude that
$
    &integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) ((- 1 + h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1 - (1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) bb(1) {Lambda^(a) ({s}) > 0} - bb(1) {Lambda^(a) ({s}) = 0}) M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s),
$
and $h(dot,a_1)$ freely chosen, predictable satisfying some integrability criteria.
Interestingly, this means that the stochastic exponential $cal(E) (K^(h))_t$ will depend on the choice of $h$ in general,
but only through $h(s, a_1)$ which can be freely chosen. 

= Score operator calculations

Let $macron(K)_t = K^*_t + bb(N)_t^a$
for a given (local) martingale $K_t^*$ with $Delta K_t^* >= -1$
and $Delta K_t^* = -1$ if and only if $t = tau^(g^*)$ and $tau^(g^*) < oo$.
Then, it is the case that $Delta macron(K)_t = bb(1) {t != tau^(g^*)} Delta K_t^*
+ bb(1) {t = tau^(g^*)} (0) > -1$ so $cal(E) (macron(K)) > 0$.
First, we see that
$
    cal(E) (K^*)_t &= cal(E) (- bb(N)^a)_t cal(E) (K^*)_t \
        &= cal(E) (K^* + bb(N)^a - bb(N)^a)_t cal(E) (- bb(N)^a)_t \
        &= cal(E) (macron(K))_t cal(E) (- bb(N)^a)_t.
$
Let $macron(W) = cal(E) (macron(K))$ and $partial_epsilon f(epsilon) = evaluated((partial)/(partial epsilon) f(epsilon))_(epsilon = 0)$.
//Thus $macron(W) = cal(E) (macron(K))$ satisfies the desired property of
//"Score operators for artificial censoring experiments".
Then, let $cal(L)$ denote the stochastic logarithm, so that
$
    1/epsilon cal(L) ((macron(W)^epsilon) / (macron(W)^0))_t &= 1/epsilon cal(L) (cal(E) (macron(K)^epsilon) cal(E) (- macron(K)^0 + sum_(0 < s <= dot) (Delta macron(K)^0_s)^2 / (1 + Delta macron(K)^0_s)))_t \
        &= 1/epsilon cal(L) (cal(E) (macron(K)^epsilon - macron(K)^0 + sum_(0 < s <= dot) (Delta macron(K)^0_s)^2 / (1 + Delta macron(K)^0_s) + [macron(K)^epsilon, - macron(K)^0 + sum_(0 < s <= dot) (Delta macron(K)^0_s)^2 / (1 + Delta macron(K)^0_s)]))_t \
        &= 1/epsilon (macron(K)_t^epsilon - macron(K)_t^0 + sum_(0 < s <= t) (Delta macron(K)^0_s)^2 / (1 + Delta macron(K)^0_s) + [macron(K)^epsilon, - macron(K)^0 + sum_(0 < s <= dot) (Delta macron(K)^0_s)^2 / (1 + Delta macron(K)^0_s)]_t) \
        &= 1/epsilon (macron(K)_t^epsilon - macron(K)_t^0 + sum_(0 < s <= t) (Delta macron(K)^0_s)^2 / (1 + Delta macron(K)^0_s) - [macron(K)^epsilon, sum_(0 < s <= dot) (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s)]_t) \
        &= 1/epsilon (macron(K)_t^epsilon - macron(K)_t^0 + sum_(0 < s <= t) (Delta macron(K)^0_s)^2 / (1 + Delta macron(K)^0_s) - sum_(0 < s <= t) Delta macron(K)_s^epsilon (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s)) \
        &-> partial_epsilon macron(K)_t^epsilon - sum_(0 < s <= t) (partial_epsilon Delta macron(K)_s^epsilon) (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s) 
$
as $epsilon -> 0$, where we use dominated convergence and L'Hopitals rule for the last step.
The result is presented in @eq:scoreoperator.

We will also need to calculate $partial_epsilon (pi_s ({a_j}) (P_epsilon))$,
which by definition fulfills that
$
    Lambda^(a,a_j) (dif t) (P_epsilon) &=  pi_t ({a_j}) (P_epsilon) Lambda^(a) (dif t) (P_epsilon),
$
where $M^a = sum_(j=1)^K M^(a, a_j)$.
Taking the derivative on both sides gives
$
    angle.l Gamma, M^(a, a_j) angle.r_t^P &= (partial_epsilon (pi_t ({a_j}) (P_epsilon)) Lambda^(a) (dif t) (P) + pi_t ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_t^P)
$
so we conclude that
$
    partial_epsilon (pi_t ({a_j}) (P_epsilon)) &= (dif angle.l Gamma, M^(a, a_j) angle.r_t^P - pi_t ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_t^P) / (dif Lambda^(a) (t) (P)) \
        &= (dif angle.l Gamma, (1-pi_dot ({a_j}) (P)) bullet M^(a, a_j) - pi_dot ({a_j}) (P) bullet sum_(i != j) M^(a, a_i) angle.r_t^P) / (dif Lambda^(a) (t) (P)) \
$
Here, we have used that using that $partial_epsilon Lambda_t (P_epsilon) = angle.l Gamma, M angle.r_t^P$
if $M = N - Lambda (P)$.

Let $m_(s,k,j)^*$ predictable be given by $m_(s,k,j)^* = bb(1) {event(k-1) < s <= event(k)} bb(1) {j = g^*_k (history(k-1), s)}$. With $K_t^* = K_(t and tau^(g*))$, we can take 
$
    macron(K)_t &= integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K bb(1) {event(k-1) < s <= event(k)} ((pi^*_(s) ({a_j}))/(pi_(s) ({a_j})) - 1) N^(a, a_j) (dif s) + bb(N)_t^a \
        &= integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K bb(1) {event(k-1) < s <= event(k)} bb(1) {j != g^*_k (history(k-1), s)} ( - 1) N^(a, a_j) (dif s) + bb(N)_t^a \
        &quad + integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* ((1)/(pi_(s) ({a_j})) - 1) N^(a, a_j) (dif s) \
        &= integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* ((1)/(pi_(s) ({a_j})) - 1) N^(a, a_j) (dif s)
$ <eq:barKrep1>
This can also be written as
$
    macron(K)_t &= integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* ((1)/(pi_(s) ({a_j})) - 1) M^(a, a_j) (dif s) + bb(L)_t^a
$ <eq:barKrep2>
Calculating the derivative of @eq:barKrep2 gives
$
    partial_epsilon macron(K)_t^epsilon &= - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) \
        &quad - integral_0^(tau and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* ((1)/(pi_(s) ({a_j})) - 1) partial_epsilon (Lambda^(a, a_j) (dif s) (P_epsilon)) + partial_epsilon bb(L)_t^a (P_epsilon) \
        &=- integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) \
        &quad - integral_0^(tau and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* ((1)/(pi_(s) ({a_j})) - 1) dif angle.l Gamma, M^(a, a_j) angle.r^P_s + angle.l Gamma, bb(L)^a angle.r^P_t \
        &= -integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) - angle.l Gamma, K^* angle.r^P_(t),
$
again using that $partial_epsilon Lambda_t (P_epsilon) = angle.l Gamma, M angle.r_t^P$
if $M = N - Lambda (P)$ is a $P$-martingale.
On the other hand also calculating it for @eq:barKrep1 gives
$
    partial_epsilon macron(K)_t^epsilon &= -integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) N^(a, a_j) (dif s) 
$
Also note that
$
    (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s) = sum_(k) sum_(j=1)^K m_(s,k,j)^* (1-pi_(s) ({a_j})) Delta N^(a, a_j) (s)
$
Thus,
$
    sum_(0 < s <= t) (partial_epsilon Delta macron(K)_s^epsilon) (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s) &= - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) 1/(pi_s ({a_j}))^2 (1-pi_(s) ({a_j})) N^(a, a_j) (dif s) \
        &=- integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) N^(a, a_j) (dif s) \
            &= - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) M^(a, a_j) (dif s) \
        &quad - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) Lambda^(a, a_j) (dif s) 
$
Conclude that, if $pi_s ({a_j}) (P) > 0$ for all $s in [0, T]$ and $j$,
$
    &partial_epsilon macron(K)_t^epsilon - sum_(0 < s <= t) (partial_epsilon Delta macron(K)_s^epsilon) (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s) \
        &=- integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s)  - angle.l Gamma, K^* angle.r^P_(t) \
        &quad + integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) M^(a, a_j) (dif s) \
        &quad + integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) Lambda^(a, a_j) (dif s) \
        &= - angle.l Gamma, K^* angle.r^P_(t) \
        &quad - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) \
        &quad + integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) Lambda^(a, a_j) (dif s) \
        &= - angle.l Gamma, K^* angle.r^P_(t) \
        &quad - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (M^(a, a_j) (dif s) - sum_v sum_i m_(s,v)^* (1/(pi_(s) ({a_i}))-1) Lambda^(a, a_i) (dif s)) \
        &= - angle.l Gamma, K^* angle.r^P_(t) \
        &quad - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (M^(a, a_j) (dif s) - sum_v sum_i (m_(s,v)^* (1/(pi_(s) ({a_i}))-1) \
            &quad quad - (0/(pi_s ({a_j})) - 1) bb(1) {event(v-1) < s <= event(v)} bb(1) {j != g^*_v (history(v-1), s)} Lambda^(a, a_i) (dif s))\
        &= - angle.l Gamma, K^* angle.r^P_(t) \
            &quad - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (M^(a, a_j) (dif s) - dif angle.l M^(a, a_j), K^* angle.r_s^P) \
            &= - angle.l Gamma, K^* angle.r^P_(t) \
            &quad  - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) angle.r_t^P - pi_t ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif angle.l M^(a, a_j), K^* angle.r_s^P) 
$ <eq:scoreoperatorfinal>
Note that $(dif angle.l Gamma, M^(a, a_j) angle.r_t^P - pi_t ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_t^P) / (dif Lambda^(a, a_j) (t) (P))$
can be be chosen predictable so that the corresponding term is a (local) martingale
and that the last two terms in @eq:scoreoperatorfinal can be written as $angle.l Gamma, Z angle.r_t^P$
for some (local) martingale $Z$ not specified (here).
Conclude that the Score operator $S$ is given by
$
    cal(L)^2 (P) in.rev Gamma &mapsto Gamma - angle.l Gamma, K^* angle.r^P_(t) \
        &quad - integral_0^(t and tau^(g^*)) sum_(k) sum_(j=1)^K m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif angle.l M^(a, a_j), K^* angle.r_s^P) in cal(L)^2 (Q)
$ <eq:scoreoperator>

Assume that we have found the adjoint operator of $D : cal(L)^2 (P) -> cal(L)^2 (Q)$
$
    cal(L)^2 (P) in.rev Gamma &mapsto Gamma - angle.l Gamma, K^* angle.r^Q_(t) in cal(L)^2 (Q) \
$
say $D^* : "Range"(D) subset cal(L)^2 (Q) -> cal(L)^2 (P)$.
Let $H_j: cal(L)^2 (P) -> cal(L)^2 (Q)$ be given by
$
    H_j Gamma = integral_0^(t and tau^(g^*)) sum_(k) m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) angle.r_t^P - pi_t ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif angle.l M^(a, a_j), K^* angle.r_s^P)
$
Then, we have that

$
    angle.l H_k Gamma, Gamma angle.r_Q &:= mean(Q) [angle.l H_k Gamma, Gamma' angle.r^Q] \
        &= mean(Q) [angle.l integral_0^(dot and tau^(g^*)) sum_(k) m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) angle.r_s^P - pi_s ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) D M^(a, a_j) (dif s), Gamma' angle.r^Q_s] \
        &= mean(Q) [angle.l D integral_0^(dot and tau^(g^*)) sum_(k) m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) angle.r_s^P - pi_s ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) M^(a, a_j) (dif s), Gamma' angle.r^Q_s] \
        &= mean(P) [angle.l integral_0^(dot and tau^(g^*)) sum_(k) m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) angle.r_s^P - pi_s ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) M^(a, a_j) (dif s), D^* Gamma' angle.r^P_s] \
        &:= mean(P) [angle.l Y_j Gamma, D^* Gamma' angle.r^P_s] \
        &= angle.l Gamma, Y_j^* D^* Gamma' angle.r_P,
$
so if we have found $D^*$ and $Y_j^*$, we have found the adjoint of $H_j$.
Here, we let
$Y_j : cal(L)^2 (P) -> cal(L)^2 (P)$ be given by
$
    Y_j Gamma = integral_0^(dot and tau^(g^*)) sum_k m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) angle.r_s^P - pi_s ({a_j}) (P) dif angle.l Gamma, M^(a) angle.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) M^(a, a_j) (dif s)
$
Then, we may calculate directly that
$
    angle.l Y_j Gamma, Gamma' angle.r_P &:= mean(P) [angle.l Y_j Gamma, Gamma' angle.r^P] \
        &= mean(P) [angle.l integral_0^(dot and tau^(g^*)) sum_k m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r^P_s) / (dif Lambda^(a, a_j) (s) (P)) dif M^(a, a_j) (s), Gamma' angle.r^P] \
        &= mean(P) [integral_0^(dot and tau^(g^*)) sum_k m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r^P_s) / (dif Lambda^(a, a_j) (s) (P)) dif angle.l M^(a, a_j), Gamma' angle.r_s^P] \
        &= mean(P) [angle.l Gamma, bb(1) {tau^(g^*) <= dot} sum_k m_(dot,k,j)^* (dif angle.l M^(a, a_j), Gamma' angle.r_dot^P)/(dif Lambda^(a, a_j) (dot) (P)) bullet (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)) angle.r^P] \
        &= mean(P) [angle.l Gamma, Y_j^* Gamma' angle.r^P]\
        &= angle.l Gamma, Y_j^* Gamma' angle.r_P,
$

Now note that
$
    D^* Gamma' &= Gamma^'_0+ [Gamma', W]_t - integral_0^t W_(s-) dif Gamma'_s \
        &= Gamma^'_0 + integral_0^t W_(s-) dif (Gamma' + [Gamma', K^*])_s \
        &= Gamma^'_t W_t - integral_0^t Gamma'_(s-) dif W_s \
        &= Gamma^'_t W_t - integral_0^t Gamma'_(s-) W_(s-) dif K^*_s \
$
by the arguments in "Projection Notes"
and integration by parts for semimartingales.
This composition yields,
$
    &integral_0^t bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* (dif angle.l M^(a, a_j), D^* Gamma' angle.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &= integral_0^t bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) (dif angle.l M^(a, a_j), Gamma' + [Gamma', K^*] angle.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s
$

FACT:
$
    angle.l X, Y angle.r^Q = angle.l X + [X, K^*], Y angle.r^P = angle.l X, Y + [Y, K^*] angle.r^P,
$
so it follows that
$
    &integral_0^t bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) (dif angle.l M^(a, a_j), Gamma' + [Gamma', K^*] angle.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &= integral_0^t bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) (dif angle.l M^(a, a_j), Gamma' angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &= integral_0^t bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) (dif angle.l M^(a, a_j), Gamma' angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (N^(a, a_j) - pi_dot ({a_j}) (P) bullet N^(a))_s.
$
Note that this operator sends to piecewise constant functions.
Note that the adjoint operator can be written as $("Id" - sum_j Y_j^*) D^*$.
If $"Id" - sum_j Y_j^*$ is injective, it holds that
$
    "ker" (S^*) = "ker" (("Id" - sum_j Y_j^*) D^*) = "ker" (D^*) = {0}
$
where the last equality follows by "Projection Notes".
So this will follow, if we can show that $"Id" - sum_j Y_j^*$ is injective.
Note that $"ker" ("Id" - sum_j Y_j^*) = "ran" ("Id" - sum_j Y_j)^perp$.
To this end, we shall show that $"Id" - sum_j Y_j$ is surjective
if $pi_s ({a_j}) (P) > 0$ for all $s in [0, T]$ and $j$.
Take $Gamma^* in cal(M)^2 (P)$;
we shall find $Gamma in cal(M)^2 (P)$ such that
$
    Gamma^* = Gamma - sum_j Y_j Gamma.
$
By the martingale representation theorem, we can write
$
    Gamma^* &= integral_0^dot sum_x gamma^*_x (s) M^(x) (dif s) \
    Gamma &= integral_0^dot sum_x gamma_x (s) M^(x) (dif s)
$
//We show that $sum_j Y_j^*$ is a contraction; this then follows
//by a fixed-point theorem.

//Another strategy: Show that $-(sum_j Y_j^* - "Id")$ is surjective.
//By Fredholms alternative, this will imply injectivity under certain regularity conditions. Alternatively,
//can try to show the same for $-(sum_j Y_j - "Id")$.

We will need to find the $angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) angle.r_t^P$ term.
$
    angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) angle.r_t^P &=  integral_0^(t) sum_x h_x (s) dif angle.l M^(x), M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) angle.r_s^P \
$
Now note that
$
    angle.l M^(x), M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) angle.r_s^P &= Lambda_s^(*,x,j) - integral_0^s Delta angle.l M^x angle.r_s dif Lambda^(a,a_j) (s) + integral_0^s pi_s ({a_j}) (P) Delta angle.l M^x angle.r_s dif Lambda^(a) (s) \
        &= Lambda_s^(*,x,a_j) - integral_0^s Delta angle.l M^x angle.r_s pi_s ({a_j}) (P) dif Lambda^(a) (s) + integral_0^s pi_s ({a_j}) (P) Delta angle.l M^x angle.r_s dif Lambda^(a) (s) \
        &= Lambda_s^(*,x,a_j)
$
where $Lambda^(*,x,a_j)$ is the compensator of $integral_0^t Delta N^x_s dif N^(a,a_j) (s) - integral_0^t pi_s ({a_j}) (P) Delta N^(x) (s)) dif N^a_s$.
If $x in.not cal(A)$, then $Lambda^(*,x,a_j) = 0$.
If $x = a_i in cal(A)$, then
$

    &integral_0^t Delta N^x_s dif N^(a,a_j) (s) - integral_0^t pi_s ({a_j}) (P) Delta N^(x) (s)) dif N^a_s \
        &= bb(1) {j=i} N^(a,a_j) (t) - integral_0^t pi_s ({a_j}) (P) dif N^(a_i) (s) \
$
This has the compensator
$
    Lambda_t^(*,x,a_j) &= bb(1) {j=i} Lambda^(a,a_j) (t) - integral_0^t pi_s ({a_j}) (P) dif Lambda^(a,a_i) (s) \
        &= bb(1) {j=i} Lambda^(a,a_j) (t) - integral_0^t pi_s ({a_i}) (P) dif Lambda^(a,a_j) (s) \
    &= integral_0^t bb(1) {j=i} - pi_s ({a_i}) (P) dif Lambda^(a,a_j) (s)
$
where the second properties works by properties of Radon-Nikodym derivatives and positivity.
Now, we have that
$
    Y_j Gamma - Gamma &= integral_0^(dot and tau^(g^*)) sum_j sum_k m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r^P_s) / (dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) )_s - integral_0^dot sum_x gamma_x (s) M^(x) (dif s) \
        &= integral_0^(dot and tau^(g^*)) sum_j sum_k m_(s,k,j)^* sum_(x in cal(A)) gamma_x (s) (bb(1) {a_j= x} - pi_s ({x}) (P))dif M_s^(a, a_j) - integral_0^dot sum_x gamma_x (s) M^(x) (dif s) \
$
Whenever $x in.not cal(A)$, we can choose $gamma_x (s) = - gamma^*_x (s)$.
Otherwise, we may pick
$
    gamma_x (s) &= bb(1) {s <= tau^(g^*)} sum_k bb(1) {event(k-1) < s <= event(k)} bb(1) {x != g^*_k (history(k-1), s)} (- gamma^*_x (s)) \
        &+ bb(1) {s <= tau^(g^*)} sum_k bb(1) {event(k-1) < s <= event(k)} bb(1) {x = g^*_k (history(k-1), s)} (- (sum_(y in cal(A), y!= x) pi_s ({y}) (P) gamma^*_y (s)) / (pi_s ({x}) (P))) \
        &+ bb(1) {s > tau^(g^*)} (- gamma^*_x (s))
$
// Now calculate
// $
//     S S^* Gamma &= (D - sum_j D Y_j)(D^* Gamma - sum_j Y_j^* D^* Gamma) \
//         &= D D^* Gamma - D sum_j Y_j^* D^* Gamma - sum_j D Y_j D^* Gamma + (sum_j D Y_j) sum_i Y_i^* D^* Gamma \
//         &= Gamma_0 + integral_0^dot macron(W)_s dif Gamma_s  - D sum_j Y_j^* D^* Gamma - (sum_j D Y_j) D^* Gamma + (sum_j D Y_j) (sum_i Y_i^* D^* Gamma) 
// $
// Note that
// $
//     (sum_j D Y_j) (sum_i Y_i^* D^* Gamma) &= sum_j sum_i D Y_j Y_i^* D^* Gamma \
//         &= sum_j sum_i integral_0^(dot and tau^(g^*)) sum_k m_(s,k,j)^* (dif angle.l Y_i^* D^* Gamma, M^(a, a_j) - pi_s ({a_j}) (P) bullet M^(a)  angle.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) \
//         &times dif (M^(a, a_j) - dif angle.l M^(a, a_j), K^* angle.r_s^P) \
//         &= sum_j sum_i integral_0^(dot and tau^(g^*)) sum_k m_(s,k,j)^* \
//         &times (bb(1) {tau^(g^*) <= s} sum_k m_(s,k,i)^* W_(s-) (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif angle.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a), M^(a, a_i) - pi_dot ({a_i}) (P) bullet M^(a) angle.r_s) / (dif Lambda^(a, a_j) (t) (P)) \
//         &= sum_j integral_0^(dot and tau^(g^*)) W_(s-) sum_k m_(s,k,j)^* (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) (dif angle.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) angle.r_s) / (dif Lambda^(a, a_j) (t) (P)) \
//         &times dif (M^(a, a_j) - dif angle.l M^(a, a_j), K^* angle.r_s^P) \
// $
// and
// $
//     D sum_j Y_j^* D^* Gamma &= D sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
//         &= sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (D (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)))_s \
//         &= sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) \
//         &times (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) - angle.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a), K^* angle.r^P)_s \
// $
// //         &= sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) \
// //         &times (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) - angle.l M^(a, a_j), K^* angle.r^P)_s \
// // $
// // Here, we use that
// // $
// //     angle.l - pi_dot ({a_j}) (P) bullet M^(a), K^* angle.r^P_t &= integral_0^(t and tau^(g^*)) sum_i (pi_s ({a_i}) - pi_s^* ({a_i}) dif angle.l M^(a, a_j), M^(a, a_i) angle.r_s^P \
// //         &= 0
// // $
// Finally, note that
// $
//     sum_j D Y_j D^* Gamma &= integral_0^(t and tau^(g^*)) W_(s-) sum_(k) sum_(j=1)^K m_(s,k,j)^* (dif angle.l Gamma + [Gamma, K^*], M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif angle.l M^(a, a_j), K^* angle.r_s^P) \
//         & integral_0^(t and tau^(g^*)) W_(s-) sum_(k) sum_(j=1)^K m_(s,k,j)^* (dif angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r_t^Q) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif angle.l M^(a, a_j), K^* angle.r_s^P)
// $
// Thus, we find
// $
//     S^* S Gamma &= sum_j integral_0^(dot and tau^(g^*)) W_(s-) sum_k m_(s,k,j)^* \
//         &quad times ((dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) ((dif angle.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) angle.r_s) / (dif Lambda^(a, a_j) (t) (P)) -1) - (dif angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r_t^Q) / (dif Lambda^(a, a_j) (t) (P))) \
//         &quad times dif (M^(a, a_j) - dif angle.l M^(a, a_j), K^* angle.r_s^P) \
//         &+sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-) pi_s ({a_j}) (P)  (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a) - angle.l M^(a), K^* angle.r^P)_s \
//         &+ Gamma_0 + integral_0^dot macron(W)_s dif Gamma_s \
//     &= sum_j integral_0^(dot and tau^(g^*)) W_(s-) sum_k m_(s,k,j)^* \
//         &quad times ((dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) ((dif angle.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) angle.r^P_s) / (dif Lambda^(a, a_j) (t) (P)) -1) - (dif angle.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  angle.r_t^Q) / (dif Lambda^(a, a_j) (t) (P))) \
//         &quad times dif (M^(a, a_j) - dif angle.l M^(a, a_j), K^* angle.r_s^P) \
//         &+sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k m_(s,k,j)^* W_(s-)  (dif angle.l M^(a, a_j), Gamma angle.r_s^Q)/(dif Lambda^(a) (s) (P)) dif (M^(a) - angle.l M^(a), K^* angle.r^P)_s \
//         &+ Gamma_0 + integral_0^dot macron(W)_s dif Gamma_s
// $

// With respect to the adjoint of the Score operator maybe conclude that
// the argument in Kjetils document shows that the adjoint gives
// my efficient influence function.


= Sequential representation of exchangeabillity

#theorem[
    Suppose consistency and positivity holds as in @thm:identifiabilitymartingale.
    Then, we have
    $
        mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t],
    $
    for all $t in [0, T]$, if for $k in bb(N)$
    and $t in [0, T]$ it holds that
    $
        tilde(Y)_t perp bb(1) {treat(k) = g^* (history(k-1), event(k))} | cal(F)^(g^*)_(event(k-1)), event(k) <= t, status(k) = a,
    $
    where
    $
        cal(F)^(g^*)_event(k) = sigma(covariate(k), status(k), bb(1) {treat(k) = g_k^* (history(k-1), event(k))), dots, bb(1) {treat(0) = g_0^*(covariate(0))}, covariate(0))
    $
]
// should be able to do it witrh F_(T_k and t)
// look at conditions with both right censoring and coarsening

#proof[
    We see immediately that,
    $
        &integral W_(s-) bb(1) {event(m) < s < event(m+1) and t} dif K_s \
            &= W_(event(m)) integral bb(1) {event(m) < s < event(m+1) and t} dif K_s \
            &= W_(event(m)) bb(1) {event(m) < t} (sum_j (pi^*_(event(m)) ({a_j})) / (pi_(event(m)) ({a_j})) - 1) N^(a, a_j) (event(m+1) and t) \
//            &= W_(event(m)) bb(1) {event(m) < t} (product_j ((pi^*_(event(m)) ({a_j})) / (pi_(event(m)) ({a_j})))^(bb(1) {treat(k) = a_j}) - 1) N^(a, a_j) (event(m+1) and t) \
            &= W_(event(m)) bb(1) {event(m) < t} ((bb(1) {treat(m) = g_m^* (history(m-1), event(m))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) N^(a, a_j) (event(m+1) and t) 
    $
    By consistency and positivity, the desired result is equivalent to 
    $
        sum_(m=0)^(oo) mean(P) [integral W_(s-) bb(1) {event(m) < s < event(m+1) and t} dif K_s tilde(Y)_t] = 0
    $
    by Lemma 4 of @ryalenPotentialOutcomes, so
    $
        &sum_(m=0)^(oo) mean(P) [integral W_(s-) bb(1) {event(m) < s < event(m+1) and t} dif K_s tilde(Y)_t] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} ((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m), event(m+1))}))- 1) N^(a, a_j) (event(m+1) and t) tilde(Y)_t] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) tilde(Y)_t | history(m), event(m+1) <= tau, status(m+1) = a]] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1) <=, status(m+1) = a] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, status(m+1) = a]] \
                        &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                            &quad times mean(P) [mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1), status(m+1)=a  | history(m), event(m+1) <= tau, status(m+1) = a] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, status(m+1) = a]] \
                    &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) times (1- 1) mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, status(m+1) = a]] \
            &= 0.
    $
]

#bibliography("references/ref.bib",style: "apa")
