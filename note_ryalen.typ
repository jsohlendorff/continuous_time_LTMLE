#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.1": arkheion
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
    #math.equation(it.body, block: true, numbering: none)#label("empty")
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
where $cal(A)$ is a measurable space;
$N^ell$ denotes a random measure for covariates $L$
on $[0, T] times cal(L)$,
where $cal(A)$ and $cal(L)$ are measurable spaces;
for instance finite subsets of $RR$ and $RR^d$.
Numerating these options,
we can take
$
    cal(A) &= {a_1, dots, a_k} \
    cal(L) &= {l_1, dots, l_m}.
$
Equivalently (in the sense that the natural filtrations are the same), we may work with the multivariate counting process
$
    N (t) = (N^y ((0, t]), N^a ((0, t] times {a_1}), dots, N^a ((0, t] times {a_k}), N^ell ((0, t] times {l_1}), dots, N^ell ((0, t] times {l_m})).
$
This proces gives rise to a filtration
$(cal(F)_t)_(t >= 0)$,
where $cal(F)_t := sigma(N (s) | s <= t)$.
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
in the sense that there are $history(k-1) times.o cal(B) ([0, T])$-measurable functions $g^*_k$
which return a treatment decision in $cal(A)$
such that
$
    pi^*_t (dif x) = sum_k bb(1) {event(k-1) < t <= event(k)} delta_(g^*_k (history(k-1), event(k))) (dif x),
$
This means that, critically,
$N^(g^*) (dif t times dif x)$ is also a random measure.
Note that $N^(g^*)$ has the compensator
$
    scr(L) (N) (dif t times dif x) = pi^*_t (dif x) underbrace(Lambda^a (dif t times cal(A)), =:Lambda^a (dif t)),
$
where $Lambda^a (dif t)$ is the $P$-$cal(F)_t$-compensator of $N^a (dif t times cal(A))$ --
also deemed the total $P$-$cal(F)_t$-compensator of $N^a$.
What this means is that
$
    N^a ((0, t] times dif x) - Lambda^a ((0, t]) times dif x)
$
is a local $P$-$cal(F)_t$-martingale.
We shall write similar notations for the other components of $N$.
Let $scr(L)$ denote the $P$-$cal(F)_t$-canonical compensator of $N^(g^*)$.
However, $N^a$ generally has the compensator $Lambda^(a) (dif t times dif x) = pi_t (dif x) Lambda^a (dif t)$.
Now define the time to deviation from the treatment regime as
$
    tau^(g^*) = inf {t >= 0 | N^a ((0, t] times {x}) != N^(g^*) ((0, t] times {x}) " for some " x in cal(A)},
$
when $cal(A) = {a_1, dots, a_k}$ consists of a finite set of treatment options.

#definition[
    Let $cal(tilde(F))_t := sigma(tilde(N)^y (dif s), tilde(N)^a (dif s times {x}), tilde(N)^ell (dif s times {y}) | s in (0, t], x in cal(A), y in cal(L))$.
    Let $Lambda$ denote the canonical $P$-$cal(F)_t$-compensator of $N$.

    A multivariate random measure $tilde(N) = (tilde(N)^y, tilde(N)^a, tilde(N)^ell)$
    is a *counterfactual random measure* under the intervention $g^*$
    if it satisfies the following conditions.
    1. $tilde(N)^a$ has compensator $scr(L) (tilde(N))$ with respect to $cal(tilde(F))_t$.
    2. $tilde(N)^x$, has the same compensator $Lambda (tilde(N))$ with respect to $cal(tilde(F))_t$ for $x in {y, ell}$.
]

Now let $(event(k))_k$ denote the ordered event times of $N$.
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

Let $N^(a, x) (t) := N^a ((0, t] times {x})$ for $x in cal(A)$ and $M^(a, x) (t) := N^(a, x) (t) - Lambda^(a, x) (t)$.
Note that @eq:rytgaard is the same likelihood ratio as in @rytgaardContinuoustimeTargetedMinimum2022.
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

// Would be nice to have some results about going back in forth between results on the compensator and the kernels in the canonical compensator
// Kjetil ment this would be possible. 

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
  // One version: Pål thinks they might be equivalent actually.
  //The $P$-$cal(H)_t$ Radon-Nikodym derivative of the compensator of $N^a$ with respect to the total $P$-$cal(H)_t$ compensator given by
  //$pi_t (dif x)$ is $cal(F)_t$-measurable.
  Let $Lambda^(a, a_j) (dif t) = pi_t ({a_j}) Lambda^(a) (dif t)$ denote the $P$-$cal(F)_t$-compensator of $N^(a, a_j)$ and $Lambda^(a,a_j)_H (dif t) = pi_t^H ({a_j}) Lambda^(a)_H (dif t)$ denote the $P$-$cal(H)_t$-compensator of $N^(a, a_j)$. $pi$ is indistinguishable from $pi^H$,
  that is for all $j in {1, dots, k}$ $P(pi_t ({a_j}) = pi_t^H ({a_j}), forall t in [0, T]) = 1$.

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
        mean(P) [Y_t W (t)] &= mean(P) [Y_t bb(1) {tau^(g^*) > t} W(t)]  \
            &=^((**)) mean(P) [tilde(Y)_t bb(1) {tau^(g^*) > t} W (t)] \
            &= mean(P) [tilde(Y)_t W (t)] \
            &= mean(P) [tilde(Y)_t mean(P) [W(t) | cal(H)_0]] \
            &= mean(P) [tilde(Y)_t W (0)] \
            &= mean(P) [tilde(Y)_t] 
    $
    where in $(**)$ we used consistency.
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

It is unclear at this point whether there exist potential outcomes processes
which fulfill the exchangeability condition and the consistency condition
for any observed data distribution of $N$.
We leave this question for future research.

== Comparison with @rytgaardContinuoustimeTargetedMinimum2022

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
Note that this is weaker than the assumptions in @rytgaardContinuoustimeTargetedMinimum2022,
as they implicitly require that _all_ martingales are orthogonal
due to their factorization of the likelihood. This is because
$cal(E) (X) cal(E) (Y) = cal(E) (X + Y)$ if and only if $[X, Y] = 0$.
This can be seen by applying Theorem 38, p. 130 of @protter2005stochastic
and using that the stochastic exponential solves a specific stochastic differential equation.

//A lingering question is whether the desired $g$-formula
//can be obtained even if the martingales are not orthogonal.
#theorem("g-formula")[
    Let, further, $Q = W(T) dot P$ denote the probability measure defined by the likelihood ratio $W(T)$ given in @eq:rytgaard.
    //    Furthermore, let $Lambda_P^x$ denote the $P$-$cal(F)_t$-compensator of $N^x$ for $x in {y, ell}$.
    Under positivity, then
    1. The $Q$-$cal(F)_t$ compensator of $N^a (dif t times dif x)$ is $pi^*_t (dif x) Lambda_P^a (dif t)$.
    2. The $Q$-$cal(F)_t$ compensator of $N^x$ is $Lambda_P^x$ for $x in {y, ell}$. // addition should be zero; by Jacods formula for likelihood ratios
]

#proof[
    First note that for a local $cal(F)_t$-martingale $X$ in $P$, we have
    $
        integral_0^t 1/(W_(s -)) dif chevron.l W, X chevron.r_s^P = chevron.l K, X chevron.r_t^P
    $ <eq:girsanov1>
    since we have that $W_t = 1 + integral_0^t W_(s -) dif K_s$; whence
    $
        chevron.l W, X chevron.r_t = chevron.l 1, X chevron.r_t + chevron.l W_(-) bullet K, X chevron.r_t = W_(t -) bullet chevron.l K, X chevron.r_t
    $ 
    With $X= M^(a, x)$, we find
    $
        chevron.l K, M^(a, x) chevron.r_t^P &= integral_0^t sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif chevron.l M_P^(a, a_j), M_P^(a, x) chevron.r_s^P \
            &= integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) dif chevron.l M_P^(a, x) chevron.r_s^P \
            &quad + sum_(j != x) integral_0^t ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif chevron.l M_P^(a, a_j), M_P^(a, x) chevron.r_s^P \
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
    The second term is a local martingale. This implies $chevron.l M^(y), K chevron.r_t^P = 0$.
    For $x=ell$ the argument is the same.
]

We now provide a sequential representation
of the exchangeability condition.
It aligns closely with the postulated exchangeability condition
in @rytgaardContinuoustimeTargetedMinimum2022;
however, notably on the conditioning set, we include
the $k$'th event time, which is not included in @rytgaardContinuoustimeTargetedMinimum2022.
We conclude that if we have independent marking for the treatment
process, the condition in @rytgaardContinuoustimeTargetedMinimum2022
is sufficient for causal identification. 

#theorem[
    Suppose consistency and positivity holds as in @thm:identifiabilitymartingale.
    Then, we have
    $
        mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t],
    $
    for all $t in [0, T]$, if for $k in bb(N)$
    and $t in [0, T]$ it holds that
    $
        tilde(Y)_t perp bb(1) {treat(k) = g^* (history(k-1), event(k))} | cal(F)^(g^*)_(event(k-1)), event(k) <= t, Delta N^a (event(k)) = 1,
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
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1) <=, Delta N^a (event(k)) = 1] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
                        &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                            &quad times mean(P) [mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1), status(m+1)=a  | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
                    &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) times (1- 1) mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
            &= 0.
    $
]

== On the existence of counterfactual processes fulfilling consistency and exchangeability

It is natural to ask oneself whether there exist counterfactual processes
for any given law of $N$ such that consistency and exchangeability holds,
that is can we extend the law of $N$ to some possibly larger sample space?
This question was already posed by @RobinsLongitudinal2001 in the discrete time setting.
If this does not hold, then, certainly, we would implicitly be imposing
restrictions on the observed data law of $N$. As the theorem below shows, it
is thus harmless to pretend that such counterfactual processes do in fact exist,
as they cannot be ruled out by the observed data law of $N$.

#theorem[
    For any law of $N$, we can construct a probability space,
    wherein a counterfactual process $tilde(N)$ and $N$ exists
    such that (strong) consistency and exchangeability holds.
    Here (strong) consistency means that
    $
        tilde(N)_t bb(1) {tau^(g^*) >= t} = N_t bb(1) {tau^(g^*) >= t} quad P-"a.s."
    $
    which implies that
    $
        integral_0^t bb(1) {s <= tau^(g^*)} dif tilde(N)_t  = integral_0^t bb(1) {s <= tau^(g^*)} dif N_t,
    $
    or
    $
        tilde(N)_(dot and tau^(g^*)) = N_(dot and tau^(g^*))
    $
] <thm:existencecounterfactuals>

#proof[
    // Do we need to check the compensator definition?
    We provide an argument somewhat analogous to the one given in Section 6 of @RobinsLongitudinal2001.
    We also consider only the case where $cal(A) = {0, 1}$ and the static intervention $g^* (history(k-1), event(k)) = 1$ for all $k$.
    First, we let $(event(k), status(k), treat(k), covariate(k))_(k in NN)$ denote the marked point process
    corresponding to $N$ and $(treat(0), covariate(0))$ be the initial values of the treatment and covariate process.
    First, we generate $covariate(0)$ from its marginal distribution.
    Next, for $a_0 = 0, 1$, we generate $(L^(a_0)(T_((1))^(a_0)),T_((1))^(a_0), Delta^(a_0)_((1))) tilde covariate(1), event(1), status(1) | treat(0) = a_j, covariate(0)$
    (for each value of $a_0$, these can be generated independently).
    Next, for each $a_0 = 0, 1$ and each $a_1 = 0, 1$ where $Delta_((1))^(a_0) = a$, we generate
    $
        &(L^(a_0, a_1)(T_((2))^(a_0, a_1)), T_((2))^(a_0, a_1), Delta^(a_0, a_1)_((2))) \
            &tilde covariate(2), event(2), status(2) | covariate(1) = l_1, treat(1) = a_1, event(1) = t_1, status(1) = s_1, treat(0) = a_0, covariate(0)
    $
    where $(l_1, t_1, s_1) = (L^(a_0)(T_((1))^(a_0)),T_((1))^(a_0), Delta^(a_0)_((1)))$
    for $Delta^(a_0)_((1)) != y$ and $T^(a_0)_((1)) < T$. If $Delta^(a_0)_((1)) = y$, put $(L^(a_0, a_1)(T_((2))^(a_0, a_1)), T_((2))^(a_0, a_1), Delta^(a_0, a_1)_((2))) = (Ø, oo, Ø)$.
    Continue in this manner.
    Then, we define $tilde(N)$ by the marked point process
    $(L^(1, dots, 1)(T_((k))^(1, dots, 1)), 1, T_((k))^(1, dots, 1), Delta^(1, dots, 1)_((k)))_(k in NN)$
    with initial values in its filtration $(1, covariate(0))$.
    Next, we construct the observed data process $N$.
    We can generate the $A$'s independently from all other considered random variables.
    Generate $treat(0)$ from its conditional distribution given $covariate(0)$.
    Then, let 
    $
        (covariate(1), event(1), status(1)) = (L^(treat(0))(T_((1))^(treat(0))), T_((1))^(treat(0)), Delta^(treat(0))_((1))).
    $
    Then, again, generate $treat(1)$ from its conditional distribution given $history(0), event(1), status(1) = a$.
    Afterwards, let
    $
        (covariate(2), event(2), status(2)) = (L^(treat(0), treat(1))(T_((2))^(treat(0), treat(1))), T_((2))^(treat(0), treat(1)), Delta^(treat(0), treat(1))_((2))).
    $
    Continue in this manner.
    By construction, we then have
    $
        (tilde(N))_(t in [0, T]) perp treat(k) | history(k-1), event(k), status(k) = a
    $
    which suffices for exchangeability because it is stronger. Next, we show consistency.
    Define
    $
        tilde(Y)_t = sum_k bb(1) {T_((k))^(1, dots, 1) <= t, Delta^(1, dots, 1)_((k)) = y}
    $
    and
    $
        Y_t = sum_k bb(1) {event(k) <= t, status(k) = y}
    $
    Now note that
    $
        Y_t bb(1) {tau^(g^*) > t} &= sum_k bb(1) {event(k) <= t, status(k) = y} bb(1) {tau^(g^*) > t} \
            &= sum_k bb(1) {event(k) <= t, status(k) = y, treat(j) = 1, forall j < k} \
            &= sum_k bb(1) {T_((k))^(1, dots, 1) <= t, Delta^(1, dots, 1)_((k)) = y, treat(j) = 1, forall j < k} \
            &= sum_k bb(1) {T_((k))^(1, dots,1) <= t, Delta^(1, dots, 1)_((k)) = y} bb(1) {tau^(g^*) > t} \
            &= tilde(Y)_t bb(1) {tau^(g^*) > t},
    $
    as desired.
] 

== Comparison with Coarsening at Random (CAR) conditions of @onrobinsformula
Maybe they are the same.
Let us define the process by $Z (t) = (N^y (t), N^ell (t), L(t), N^a (t), A(t))$.
Consider also its potential outcome process $tilde(Z) = (tilde(N)^y, tilde(N)^ell, tilde(L), tilde(N)^a, 1)$.
These are both multivariate cadlag processes.
Critically, we take $cal(F)_t = sigma(Z (s), s <= t)$
-- the natural filtration of the observed data process
and $cal(H)_t = cal(F)_t or sigma(tilde(Z) (dot))$.
For simplicity, we consider only the static intervention $g^* (history(k-1), event(k)) = 1$ for all $k$.

@onrobinsformula introduces a Coarsening at Random (CAR) condition
which in our setting can be stated as follows
$
    p_(tau^(g^*)) (t | tilde(Z) = tilde(z) ) = h (t, tilde(z)_(dot and t))
$ <eq:car>
for some measurable function $h: [0, T] times D_[0, T] (RR^d) -> [0, 1]$,
where $D_[0, T] (RR^d)$ denotes the space of càdlàg functions from $[0, T]$ to $RR^d$.
The conditional distributions exist since the sample space is Polish.
It is assumed in @onrobinsformula that
$
    P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) = p_(tau^(g^*)) (t | tilde(Z) = tilde(z)) mu (dif t),
$ <eq:car2>
for some sigma-finite measure $mu$ on $[0, T]$
that does not depend on $tilde(z)$.
Note that 
$
    P(tau^(g^*) <= t | tilde(Z) = tilde(z)) = sum_k P(event(k) <= t, status(k) = a, treat(k) = 0, treat(k-1) = dots = treat(0) = 1 | tilde(Z) = tilde(z))
$
as a consequence, we have
$
    P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) &= sum_k P(event(k) in dif t, status(k) = a, treat(k) = 0, treat(k-1) = dots = treat(0) = 1 | tilde(Z) = tilde(z)) \
        &= sum_k P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
        &quad times P(event(k) in dif t, status(k) = a | treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
        &= sum_k P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
        &quad times bb(1) (t_k in dif t, delta_k = a). 
$ <eq:carseq>
This is because given everything else $event(k) in dif t, status(k) = a$ is a measurable function of $tilde(Z)$
if deviation has not occured yet. 
However, due to @eq:carseq, we see that we do, in fact, not
have @eq:car2 (formal argument missing) if the $t_k$'s do not have a discrete distribution. 
One may try to relax @eq:car to the Markov kernel 
$
    P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) = k_(tilde(z)) (dif t) = k_z^* (dif t)
$
depends on $tilde(z)$ only through $z$.
// What this means is that there is a Markov kernel $k^*$ such that
// $
//     P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) = k^*_(z_(dot and tau^(g^*))) (dif t).
// $
However, is not clear what the gain of such a condition we are no longer guaranteed a result like Theorem 2.1
of @onrobinsformula.
What @eq:carseq suggests is that we work with the following sequential condition:
$
    tilde(Z) perp treat(k) | event(k), status(k) = a, cal(F)_(event(k-1))^(a=1),
$ <eq:sequentialcar>
where $cal(F)_t^(a=1) = sigma((N^y (s), N^ell (s), L(s), N^a (s), 1), s <= t)$.

From now on, we work with this sequential condition @eq:sequentialcar
instead of @eq:car.

#theorem[
    We have that @eq:sequentialcar if and only if $bb(1) {t <= tau^(g^*) } pi_t (1)$,
    the Radon-Nikodym derivative $pi_t (1)$ of $Lambda^(a, 1)$ with respect to $Lambda^(a)$
    with respect to the filtration $cal(H)_t$ is $cal(F)_t$-adapted.
]
#proof[
    This Radon-Nikodym derivative has a version given by 
    $
        pi_(t) (1) = sum_k bb(1) {event(k-1) < t <= event(k)} P(treat(k) = 1 | history(k-1),  status(k) = a, event(k) = t, tilde(Z)).
    $
    This follows by Theorem 4.1.11 of @last1995marked. Therefore, in general,
    $
        &bb(1) {t <= tau^(g^*) } pi_t (1) \
            &= sum_k bb(1) {event(k-1) < t <= event(k)} bb(1) {t <= tau^(g^*)} P(treat(k) = 1 | history(k-1),  status(k) = a, event(k) = t, tilde(Z)) \
            &= sum_k bb(1) {event(k-1) < t <= event(k)} bb(1) {t <= tau^(g^*)} P(treat(k) = 1 | event(k) = t, status(k) = a, cal(F)_(event(k-1))^(a=1), tilde(Z)).
    $
    From this, we see that the if-part follows immediately.
    For the only if part, we see that
    $
        &bb(1) {event(k-1) < t} bb(1) {t <= tau^(g^*) and event(k)} pi_t (1) \
        &bb(1) {event(k-1) < t <= event(k)} bb(1) {t <= tau^(g^*) } pi_t (1) \
            &= bb(1) {t <= tau^(g^*) } bb(1) {event(k-1) < t <= event(k)} P(treat(k) = 1 | event(k) = t, status(k) = a, cal(F)_(event(k-1))^(a=1), tilde(Z))
    $
    Using that $bb(1) {t <= tau^(g^*) } pi_t (1)$ is $cal(F)_t$-measurable
    and hence $bb(1) {t <= tau^(g^*) and event(k)} pi_t (1)$ is $cal(F)_(event(k))$-measurable,
    we have by definition of stopping time $sigma$-algebra that $bb(1) {event(k-1) < t} bb(1) {t <= tau^(g^*) and event(k)} pi_t (1)$
    is $history(k-1)$-measurable.
    We conclude that, too, $P(treat(k) = 1 | event(k) = t, status(k) = a, cal(F)_(event(k-1))^(a=1), tilde(Z))$ must be $history(k-1)$-measurable
    for all $t$ with $event(k-1) < t <= event(k)$ and $t <= tau^(g^*)$.
    This is all in the support (?).
]

Note that if one exchangeability in terms of @thm:identifiabilitymartingale holds,
then both identification formulas are the same i.e.,
$
    mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t] = mean(P) [tilde(W)_t Y_t],
$

#theorem[
    Consider the static intervention with $g^* (history(k-1), event(k)) = 1$ for all $k$.
    and $cal(A) = {0, 1}$.
    Suppose consistency for $tilde(Y)_t$ as in @thm:identifiabilitymartingale.
    Let $pi^cal(H)_t (1)$, $pi^cal(F)_t (1)$
    denote the Radon-Nikodym derivatives of $Lambda^(a, 1)$
    with respect to $Lambda^(a)$
    in the filtrations $cal(H)_t$ and $cal(F)_t$, respectively.
    Similarly, let $Lambda^(a, cal(H))$, $Lambda^(a, cal(F))$
    denote the compensators of $N^a$ in the filtrations $cal(H)_t$
    and $cal(F)_t$, respectively.
    Suppose that a version of $pi_s^cal(F))$ exists such that
    $
        pi_s^cal(F) (1, omega) < 1
    $ <eq:nonperfectcompliance>
    for all $s in [0, T]$ and $omega in Omega^*$ with $P(Omega^*) = 1$.
    Also, suppose that strong consistency holds for $tilde(N)_t^a$, i.e.,
    $
        tilde(N)_dot^a bb(1) {tau^(g^*) >= dot} = N_dot^a bb(1) {tau^(g^*) >= dot} quad P-"a.s."
    $
    Let $cal(H)_t$ denote the initial expansion of
    $cal(F)_t$ with $sigma(tilde(N)_dot^a, tilde(Y)_dot)$.
    If the compensator of $bb(N)^a$ in the filtration $cal(H)_t$ is 
    $cal(F)_t$-predictable, then $N^a (dot and tau^(g^*))$
    is $cal(F)_t$-predictable.
]
#proof[

// Then, we have that
// $
//     mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t]
// $
// by @thm:identifiabilitymartingale if $W_dot$ is a uniformly integrable martingale.

// However, note that
// $
//     bb(L)_t^a &= integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a) (dif s) \
//         &= integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s).
// $ <eq_bbL>
// is a $cal(H)_t$-compensator of $bb(N)^a$.
// Here, we use that the compensator of $bb(1) {bb(N)_(s-)^a = 0} N^a (dif s)$
// is $bb(1) {bb(N)_(s-)^a = 0} N^a (dif s)$ itself in the filtration $cal(H)_t$.
// If $tilde(W)_t = cal(E) (-bb(K)^a)_t$ is such that it is a $P$-$cal(H)_t$-martingale (integrability conditions),
// then it will be a $P$-$cal(F)_t$-martingale as well,
// where $bb(K)^a_t = integral_0^t 1/(1 - Delta bb(L)_s^a) dif bb(M)_s^a$,
// by the stated argument since the compensator of $bb(N)^a$ in $cal(H)_t$
// is also $cal(F)_t$-adapted.
// Nonetheless, @eq_bbL in itself almost never be $cal(F)_t$-predictable,
// leading to possible issues -- also about the existence of such a $bb(L)^a$
// if treatment compensator is continuous in $cal(F)_t$, then it will almost never be able to the above?
// Conclude that if this is the case, then exchangeability in Påls setting can never hold.

Note that, under the stated conditions
$
        integral_0^dot bb(1) {s <= tau^(g^*)} N^(a) (dif s)
$
is a $cal(H)_t$-predictable process.
Therefore, it is its own compensator in $cal(H)_t$.
Now note that
$
    bb(L)^cal(H)_dot &= integral_0^dot  (1-pi^(cal(H))_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(H)) (dif s) \
        &= integral_0^dot  (1-pi^(cal(H))_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s).
$
On the other hand,
$
    bb(L)_dot^cal(F) &= integral_0^dot  (1-pi^(cal(F))_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s) 
$
Conclude that if $bb(L)^cal(H)$ is indistinguishable from $bb(L)^cal(F)$,
then
$
    (1-pi^(cal(H))_dot (1)) bb(1) {dot <= tau^(g^*)} Delta N^a (dot) = (1-pi^(cal(F))_dot (1)) bb(1) {dot <= tau^(g^*)} Delta Lambda^(a,cal(F)) (dot).
$
Therefore,
$
    bb(L)^cal(H)_dot = integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
$
on a set up to $P$-indistinguishability.
If this were $cal(F)_t$-predictable, then
$
    bb(L)^cal(H)_dot &= integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
        &= integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} M^(a, cal(F)) (dif s) + integral_0^t  (1-pi^(cal(F))_s (1)) Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s) 
$
Conclude that since
$integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} M^(a, cal(F)) (dif s)$
is a difference of two non-decreasing processes, and hence of finite variation,
a local martingale,
by p. 115 of @protter2005stochastic that 
$
    integral_0^dot (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) = integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s).
$
Then, we have that $bb(1) {dot <= tau^(g^*)} Delta Lambda^(a,cal(F)) (T^a_(k)) = -1$ by @eq:nonperfectcompliance
for all jump times $T_(k)^a$ of $N^a$.
However, we also have that
$
    bb(1) {s <= tau^(g^*)} Delta Lambda^(a,cal(F)) (s) = 0
$
whenever $s$ is not a jump time of $N^a$ by @eq:nonperfectcompliance.
This shows the statement for the discrete part of the compensator.
For the continuous part, we are now able to conclude from these two parts that
$
    integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} lambda^(a, cal(F)) (s) dif s = 0
$
from which we conclude that
$
        bb(1) {s <= tau^(g^*)} lambda^(a, cal(F)) (s) = 0
$
for almost all $s$ with respect to the Lebesgue measure
    and almost all $omega in Omega^(**)$ with $P(Omega^(**)) = 1$.
However, these two restrictions exactly mean that $bb(1) {s <= tau^(g^*)} N^a (dif s)$
is a $cal(F)_t$-predictable process.
]

This is because
$
    bb(L)_t^a = integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} M^(a) (dif s) + integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a) (dif s).
$
which implies under regularity conditions that $bb(1) {s <= tau^(g^*)} N^a (dif s)$
is a predictable process in $cal(F)_t$.
Now, we calculate
$
    bb(K)_t^a &= -integral_0^t 1/(1 - Delta bb(L)_s^a) dif bb(M)_s^a \
        &= -integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(M)_s^a \
        &= -integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(N)_s^a \
        &+ integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(L)_s^a \
        &=- integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(N)_s^a \
        &+ integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) (1-pi_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
        &=- integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(N)_s^a \
        &+ integral_0^t 1/(pi_s (1)) (1-pi_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
        &= K_t^*
$

On the other hand, the same argument shows that if the other exchangeability condition holds
then $pi_s (1) bb(1) {s <= tau^(g^*)}$ can be chosen $cal(F)_t$-adapted,
since we can pick
$
    pi_s (1) = sum_k bb(1) {event(k-1) < s <= event(k)} (1- Delta bb(L)_(event(k-1))^a) //(0 bb(1) {status(k-1) = a, event(k-1) > tau^(g^*)} + (1- Delta bb(L)_(event(k-1))^a) bb(1) {status(k-1) = a, event(k-1) <= tau^(g^*)}).
$
By construction, $pi_s (1)$ is the desired Radon-Nikodym derivative with respect to $cal(H)_t$.
Moreover, it is $cal(F)_t$-adapted since $Delta bb(L)_(event(k-1))^a$ is $cal(F)_(event(k-1))$-measurable.x
Therefore, again, the weight $W(t)$ is a $P$-$cal(H)_t$-martingale as well
and $cal(F)_t$-adapted under integrability conditions.
Therefore, we have that
$
    mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t]
$
also. Now calculate
$
    K_t^* &= integral_0^t bb(1) {s <= tau^(g^*)} (1/(pi_s (1)) - 1) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &= integral_0^t bb(1) {s <= tau^(g^*)} sum_k bb(1) {event(k-1) < s <= event(k)} (1/(pi_s (1)) - 1) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &= sum_k integral_(event(k-1) and t)^(event(k) and t) bb(1) {s <= tau^(g^*)} (1/(1-Delta bb(L)_(event(k-1))^a ) - 1) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &=  sum_k integral_(event(k-1) and t)^(event(k) and t) bb(1) {s <= tau^(g^*)} (Delta bb(L)_(event(k-1))^a)/(1-Delta bb(L)_(event(k-1))^a ) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &= bb(K)_t^a.
$

// #theorem[
// CAR holds if and only if for each $k in bb(N)$
//     $
//         tilde(Z) perp treat(k) | event(k), status(k) = a, cal(F)_(event(k-1))^(a=1),
//     $
//     where $cal(F)_t^(a=1) = sigma((N^y (s), N^ell (s), L(s), N^a (s), 1), s <= t)$.
// ]
// Note that 
// $
//     P(tau^(g^*) <= t | tilde(Z) = tilde(z)) = sum_k P(event(k) <= t, status(k) = a, treat(k) = 0, treat(k-1) = dots = treat(0) = 1 | tilde(Z) = tilde(z))
// $
// as a consequence, we have
// $
//     P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) &= sum_k P(event(k) in dif t, status(k) = a, treat(k) = 0, treat(k-1) = dots = treat(0) = 1 | tilde(Z) = tilde(z)) \
//         &= sum_k P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &quad times P(event(k) in dif t, status(k) = a | treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &= sum_k P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &quad times bb(1) (t_k in dif t, delta_k = a). 
// $ <eq:carseq>
// This is because given everything else $event(k) in dif t, status(k) = a$ is a measurable function of $tilde(Z)$
// if deviation has not occured yet. 
// Since, under the assumption, we have that,
// $
//     &P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &= P(treat(k) = 0 | event(k) = t, status(k) = a, cal(F)_(event(k-1))^(a=1) = f_(t_(k-1))^(a=1)) \
// $
// then CAR holds using consistency.

// Conversely assume that CAR holds.
// From @eq:carseq, we have that
// $
//     &bb(1) {t_(k-1) < t <= t_k} P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) \
//         &= P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &times bb(1) {t_(k-1) < t <= t_k} bb(1) {t_k in dif t, delta_k = a}.
// $
// , where $cal(F)_(event(k-1))^(- "a")$ is the stopping time $sigma$-algebra
// for the natural filtration without the treatment process $A(t)$.
// For this one, it suffices
// that
// $
//     treat(k) perp tilde(Z) | event(k), status(k) = a, treat(k-1) = dots = treat(0) = 1, cal(F)_(event(k-1))^("a" = 1)
// $
// for each $k$, which is what we were working with $tilde(Y)$ instead of $tilde(Z)$.
// However, the only thing I needed to use was that $bb(1) {event(k) <= t, status(k) = a}$ is a measurable function of $tilde(Z)$
// of $treat(k-1) = dots = treat(0) = 1$.
// Maybe these two are equivalent?




// For given laws of $N$ with a perfect compliance at baseline,

// Consider the simple mark point process $(event(2), treat(1), status(1), event(1), covariate(0))$.
// We show that there exist settings in which CAR does not hold,
// but the exchangeability condition of @thm:identifiabilitymartingale does hold.
// We may generate a potential outcome process $tilde(N)$
// as in the proof of @thm:existencecounterfactuals
// with baseline covariate $covariate(0)$. We show that our exchangeability condition holds for the filtration
// that does not include $covariate(0)$, but CAR does not hold.
// We choose $P(treat(1) = 1 | event(1), status(1) = a, treat(0) = 0, covariate(0) = 0) = 1/2$
// which by our construction will also mean that $P(treat(1) = 1 | event(1), status(1) = a, treat(0) = 0, covariate(0) = 1, tilde(N) = tilde(n)) = 1/2$.
// Need to also construct it such that
// $
//     &g^0 (t) = P (event(1) <= t, status(1) = a | tilde(T)_2 = t_2, covariate(0) = 0) = P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 0) \
//         &!= P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 1) = P (event(1) <= t, status(1) = a | tilde(T)_2 = t_2, covariate(0) = 1) = g^1 (t)
// $
// for example if the distribution of $event(2)$ depends only on $covariate(0), status(k) = a$ and only on $event(1)$ through the relation $event(2) > event(1)$,
// this will hold I think. Explicitly find this distribution with Bayes formula probably.
// Then,
// $
//     P (tau^(g^*) <= t | tilde(N) = tilde(n) ) &= P (event(1) <= t, status(1) = a, treat(1) = 0 | tilde(N) = tilde(n) ) \
//         &= mean(P) [P (event(1) <= t, status(1) = a, treat(1) = 0 | tilde(N) = tilde(n), covariate(0))| tilde(N) = tilde(n)] \
//         &= mean(P) [P(treat(1) = 0 | event(1) <= t, status(1) = a, tilde(N) = tilde(n), covariate(0)) \
//             &times P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0)) | tilde(N) = tilde(n)] \
//         &= mean(P) [1/2 P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0)) | tilde(N) = tilde(n)] \
//         &= 1/2 P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 0) P(covariate(0) = 0 | tilde(N) = tilde(n)) \
//         &+ 1/2 P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 1) (1-P(covariate(0) = 0 | tilde(N) = tilde(n))) \
    
// $
// This shows the desired statement ... just need to come up with some distributions. 
// In the next example construct it such that
// $
//     P (event(1) <= t, status(1) = a, treat(1) = 0 | tilde(N) = tilde(n)) = h (t)
// $
// while
// $
//     P (event(1) <= t, status(1) = a, treat(1) = 1 | tilde(N) = tilde(n), covariate(0)) != h (t)
// $

== Comparison between @ryalenPotentialOutcomes and @rytgaardContinuoustimeTargetedMinimum2022

Consider a simple example where $N^a (t) <= 1$ for all $t$,
and consists of the multivariate counting process $N = (N^y, N^(a,a_0), N^(a,a_1))$.
We consider the intervention $pi^*_t (a_1) = 1$ for all $t$.
Suppose that $(N^y, N^(a,a_0), N^(a,a_1))$ has compensator
$
    Lambda^y (dif t) (P) &= lambda_t^y dif t, \
    Lambda^(a,a_j) (dif t) (P) &= pi_t (a_j) lambda_t^a dif t, j=0,1.
$
with respect to $cal(F)_t$ in $P$.
In $P$, note that
$
    mean(P) [Y_t] &= mean(P) [N^y (t)] \
        &= mean(P) [bb(1) {event(1) <= t, status(1) = y} \
            &+ bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}\
            &+ bb(1) {status(1) = a, treat(1) = 0, event(2) <= t, status(2) = y}]\
        &= integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a,a_1) + lambda_u^(a,a_0)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a,a_1) + lambda_u^(a,a_0)) dif u) lambda_s^(a,a_1) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y ) dif u) lambda_v^y dif v dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a,a_1) + lambda_u^(a,a_0)) dif u) lambda_s^(a,a_0) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y ) dif u) lambda_v^y dif v dif s \
$

Then, in $Q$, we have
$
    Lambda^y (dif t) (Q) &= lambda_t^y dif t, \
    Lambda^(a,a_0) (dif t) (Q) &= 0, \
    Lambda^(a,a_1) (dif t) (Q) &= lambda_t^a dif t.
$
Therefore,
$
    mean(Q) [Y_t] &= mean(Q) [N^y (t)] \
        &= mean(Q) [bb(1) {event(1) <= t, status(1) = y} \
            &+ bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}]\
        &= integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
        &= integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) \
        &quad times (1-exp(- integral_s^t lambda_u^y dif u)) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) - integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^a dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) \
        &quad times (1-exp(- integral_s^t lambda_u^y dif u)) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) exp(- integral_s^t lambda_u^y dif u) dif s \
        &=^(!) 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) \
        &- exp(-integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (lambda_u^(a)) dif u) lambda_s^(a) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) \
        &- exp(-integral_0^t lambda_u^y dif u) (1-exp(- integral_0^t (lambda_u^(a)) dif u)) \
        &= 1 - exp(- integral_0^t lambda_u^y dif u)
$
In (!) use that $lambda^y (u)$ does not depend on $s$ at all (jump time $a$).
With constant intensities and constant treatment probabilities, this reduces to
$
    mean(Q) [Y_t] &= integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^y dif s \
        &+ integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^(a) \
        &quad times (1-exp(- lambda^y (t-s))) dif s \
        &= (lambda^y /(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) \
        &+ (lambda^(a)/(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) - lambda^(a) exp(- lambda^y t)/(lambda^a) (1-exp(- lambda^a t)) \
        &= (1-exp(- (lambda^y + lambda^(a)) t)) - exp(- lambda^y t)(1-exp(- lambda^a t)) \
        &= 1 - exp(- lambda^y t) 
$
Now consider "a going to the Tivoli example" in which
the visit itself directly affects the probability of dying.
$
    mean(Q) [Y_t] &= integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^y dif s \
        &+ integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^(a) \
        &quad times (1-exp(- lambda^(y,2) (t-s))) dif s \
        &= (lambda^y /(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) \
        &+ (lambda^(a)/(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) - lambda^(a) exp(- lambda^(y,2) t)/(lambda^a+lambda^y+lambda^(y,2)) (1-exp(- (lambda^a + lambda^y+lambda^(y,2)) t)) \
        &= 1-exp(- (lambda^y + lambda^(a)) t) - lambda^(a) exp(- lambda^(y,2) t)/(lambda^a+lambda^y-lambda^(y,2)) (1-exp(- (lambda^a + lambda^y-lambda^(y,2)) t))
$

However, in $tilde(Q)$ (Ryalen), we have
$
    Lambda^y (dif t) (tilde(Q)) &= (lambda_t^y dif t-0)/(1-0), \
    Lambda^(a,a_0) (dif t) (tilde(Q)) &= (0-0)/(1-0) \
    Lambda^(a,a_1) (dif t) (tilde(Q)) &= (lambda_t^a dif t - (1-pi_(t and tau^(g^*))(a_1)) lambda^a_(t and tau^(g^*)) dif t)/(1-0) = pi_(t and tau^(g^*))(a_1) lambda^a_(t and tau^(g^*)) dif t = pi_(t)(a_1) lambda^a_(t) dif t.
$
since $tau^(g^*) = oo$ almost surely in $tilde(Q)$.
With constant intensities, we get the same as above plugging in $pi lambda^a$ instead of $lambda^a$.
Therefore,
$
    mean(tilde(Q)) [Y_t] &= mean(tilde(Q)) [N^y (t)] \
        &= mean(tilde(Q)) [bb(1) {event(1) <= t, status(1) = y} \
            &+ bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}]\
        &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
        &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times (1-exp(- integral_s^t lambda_u^y dif u))  dif s \ 
$
We now consider a more natural example, where the difference is due to time-varying confounding.
Påls functional can be written as
$
    &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) (lambda_v^y + lambda^ell_v integral_v^t exp(- integral_v^w lambda_u^y (ell_2; v) dif u) lambda^y_w (ell_2; v) dif w) dif v dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
        &quad times (lambda_v^y (ell_1 ; s) + pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) integral_v^t exp(- integral_v^w lambda_u^y (ell_1 ; s) dif u) lambda^y_w (ell_1; s) dif w) dif v dif s \
        &=integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) (lambda_v^y + lambda^ell_v (1- exp(- integral_v^t lambda_u^y (ell_2; v) dif u))) dif v dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
        &quad times (lambda_v^y (ell_1 ; s) + pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) (1-exp(- integral_v^t lambda_u^y (ell_1 ; s) dif u)) dif v dif s \
$
Can we conclude this result does not depend on $pi_t (a_1)$?
Now, note that
$
    &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
        &=[- exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u)]_0^t - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) (pi_s (a_1) lambda_s^(a) + lambda_s^ell) dif s \
        &= 1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) (pi_s (a_1) lambda_s^(a) + lambda_s^ell) dif s \    
$
Conclude that the previous is equal to
$
    &1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
        &-integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(- integral_s^t (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))) dif s \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
        &quad times pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) exp(- integral_v^t lambda_u^y (ell_1 ; s) dif u) dif v dif s \
    &=1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
        &-integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(- integral_s^t (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))) dif s \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times exp(-integral_s^t lambda_u^y (ell_1; s) dif u) (1-exp(- integral_s^t (pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u)) dif s \
$
$
        &1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
            &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y (ell_1; s) dif u) dif s \
    &=1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y (ell_1; s) dif u) dif s 
$
Partiel integration.
Let there be constant intensities,
i.e.,
$
    lambda_u^y = lambda^(y), \
    lambda_u^y (ell_i; s) = lambda^(y,*) (ell), \
    pi_u (a_1) = pi, \
    lambda_u (a_1) = lambda^(a), \
    lambda_u^ell = lambda^(ell).
$
This simplifies further to:
$
    &1 - exp(- (lambda^(y) + lambda^(ell)) t) \
        &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
        &quad times integral_s^t exp(- (lambda^(y) + lambda^(ell)) (v-s)) lambda^(ell) exp(- lambda^(y,*) (ell) (t-v)) dif v dif s \
        &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) lambda^(ell) exp(- lambda^(y,*) (ell) (t-s)) dif s \
        &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
        &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
        &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) integral_s^t exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) v)  dif v dif s \
        &- exp(- lambda^(y,*) (ell) t) lambda^(ell) (1- 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
            &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
        &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
        &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
        &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1- exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
    

$
Note that
$
    &integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
        &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
        &=exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(- pi lambda^(a) s) pi lambda^(a) \
        &quad times   (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
        &=pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) s)  \
        &- pi lambda^(a) exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(-  pi lambda^a s)  \
        &= pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell))) (1- exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) t) \
            &- pi lambda^(a) exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/(pi lambda^a) (1- exp(-  pi lambda^a t)) \

$
Collecting the terms
$
    &1 - exp(- (lambda^(y) + lambda^(ell)) t) \
        &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
        &quad times integral_s^t exp(- (lambda^(y) + lambda^(ell)) (v-s)) lambda^(ell) exp(- lambda^(y,*) (ell) (t-v)) dif v dif s \
        &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) lambda^(ell) exp(- lambda^(y,*) (ell) (t-s)) dif s \
        &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
        & quad - pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell))) (1- exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) t) \
            &+ exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (1- exp(-  pi lambda^a t)) \
            &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1- exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
            &=1 - exp(- (lambda^(y) + lambda^(ell)) t) (1 - lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
            &- exp(- (lambda^(y) + pi lambda^a + lambda^ell) (t)) lambda^(ell) (1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) - 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) \
                &quad - pi lambda^(a) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)))) \
            &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1 + pi lambda^(a) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
            &=1 - exp(- (lambda^(y) + lambda^(ell)) t) (1 - lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
            &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + lambda^ell)) 

$
which is constant in $pi$.
If $lambda_u^y (ell_1; s) = lambda_u^y (ell_2; v) = lambda_u^y$, then this reduces to
$
       &1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
           &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) (exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) - exp(- integral_s^t (lambda_u^y) dif u)) dif s \
           &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y dif u) dif s \
           &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
           &+ exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) (exp(- integral_s^t (lambda_u^ell) dif u) - 1) dif s \
           &- exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell dif s \
    &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
           &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) dif s \
           &- exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) (lambda_s^ell + pi_s (a_1) lambda_s^(a)) dif s \
    &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
           &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u) (1-exp(- integral_0^t (pi_u (a_1) lambda_u^(a)) dif u)) \
           &- exp(- integral_0^t lambda_u^y dif u) (1-exp(- integral_0^t (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) \
               &=     1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
           &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u)  \
           &- exp(- integral_0^t lambda_u^y dif u) \

$
// The difference can be written as
// $
//     mean(tilde(Q)) [Y_t] - mean(Q) [Y_t] &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) (1 - exp(- integral_0^s (pi_u (a_0) lambda_u^(a)) dif u)) lambda_s^y dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) (1 - exp(- integral_0^s (pi_u (a_0) lambda_u^(a)) dif u)) (pi_s (a_1) lambda_s^(a) \
//             &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//             &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//             &+integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) exp(- integral_0^s (pi_u (a_0) lambda_u^(a)) dif u) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //     &=integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^s (pi_u (a_0) lambda_u^(a)) dif u) - 1) lambda_s^y dif s \
//         // &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^s (pi_u (a_0) lambda_u^(a)) dif u)-1) (pi_s (a_1) lambda_s^(a) \
//         //     &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //     &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) pi_s (a_0) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //     &=integral_0^t integral_0^s exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) dif w) lambda_s^y dif s \
//         //     &+ integral_0^t integral_0^s exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) dif w) (pi_s (a_1) lambda_s^(a) \
//         //     &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //         &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) pi_s (a_0) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //         &=integral_0^t integral_w^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u)  lambda_s^y dif s exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) dif w \
//         //         &+ integral_0^t integral_w^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) integral_s^v exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v pi_s (a_1) lambda_s^(a) dif s \
//         //         &quad times (exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) )  dif w\
//         //     &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) pi_s (a_0) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s 
// $
If we could find an example where the above is non-zero, then we would by the construction
in "existence of counterfactuals" have found an example where Påls exchangeability does not hold and mine does. 

= More general exchangeability conditions

We now consider more general exchangeability conditions.
#theorem[
    Let $Q_kappa = cal(E) (kappa)_T dot P$ where $kappa$ is a local $P$-$cal(F)_t$ martingale
    with $Delta kappa_t >= -1$.
    If
    1. Consistency holds as in @thm:identifiabilitymartingale.
    2. $cal(E) (kappa)_t cal(E) (-bb(N)^a)_t = cal(E) (kappa)_t$ for all $t in [0, T]$ $P$-a.s.
    3. $Q_kappa$ is a uniformly integrable $P$-$cal(F)_t$-martingale and $P$-$cal(H)_t$-martingale, where $cal(H)_t = cal(F)_t or sigma(tilde(Y))$.
    Then,
    $
        mean(P) [tilde(Y)_t] = mean(P) [Y_t cal(E) (kappa)_t]
    $
] <thm:identifiabilitygeneral>
#proof[
    The proof is the same as in @thm:identifiabilitymartingale -- mutatis mutandis.
]

We provide an equivalent characterization of condition 2 in the above theorem
which gives direct interpretability of that condition
in the sense that it should induce a probability measure $Q_kappa$
under which the time to deviation from the treatment regime is infinite almost surely.

#lemma[
    $Q_kappa (tau^(g^*) = oo) = 1$ if and only if $cal(E) (kappa)_t cal(E) (-bb(N)^a)_t = cal(E) (kappa)_t$ for all $t in [0, T]$ $P$-a.s.
]
#proof[
    "If" part:
    $
        Q_kappa (tau^(g^*) = oo) &= mean(P) [cal(E) (kappa)_T bb(1) {tau^(g^*) = oo}] \
            &= mean(P) [lim_(t -> oo) cal(E) (kappa)_t bb(1) {tau^(g^*) > t}] \
            &= mean(P) [lim_(t -> oo) cal(E) (kappa)_t] \
            &= mean(P) [cal(E) (kappa)_T] = 1.
    $
    "Only if" part:
    Suppose that $Q_kappa (tau^(g^*) = oo) = 1$.
    Then for every $t in [0, T]$,
    $
        mean(P) [cal(E) (kappa)_t bb(1) {tau^(g^*) > t}] &= mean(P) [mean(P) [cal(E) (kappa)_T | cal(F)_t] bb(1) {tau^(g^*) > t}] \
            &= mean(P) [cal(E) (kappa)_T bb(1) {tau^(g^*) > t}] \
            &= Q(tau^(g^*) > t) \
            &= 1.
    $
    On the other hand,
    $mean(P) [cal(E) (kappa)_t] = mean(P) [mean(P) [cal(E) (kappa)_T | cal(F)_t]] = mean(P) [cal(E) (kappa)_T] = 1$.
    Conclude that
    $
        mean(P) [cal(E) (kappa)_t (1 - bb(1) {tau^(g^*) > t})] = 0.
    $
    The integrand on the left hand side is non-negative and so it must be zero $P$-a.s.
]

#theorem[
    Let $kappa_t$ be a (local) martingale with $Delta kappa_t >= -1$
    and $Delta kappa_t^* > -1$ if $t < tau^(g^*)$. Then, 
$
    W_t^* := cal(E) (kappa)_t = cal(E) (kappa)_t cal(E) (- bb(N)^a)_t quad P-"a.s."
$
    if and only if
$
    bb(1) {tau^(g^*) < oo} kappa_(tau^(g^*)) = - bb(1) {tau^(g^*) < oo} quad P-"a.s."
$
]
#proof[
    Using the well-known formula $cal(E) (X) cal(E) (Y) = cal(E) (X + Y + [X, Y])$,
    we have
    $
        cal(E) (kappa) = cal(E) (kappa - bb(N)^a - [kappa, bb(N)^a])
    $
    This holds if and only if
    $
        1 + integral_0^t W_(t -) dif kappa_s = 1 + integral_0^t W_(t -) dif (kappa_s - bb(N)^a_s - [kappa, bb(N)^a]_s)
    $
    if and only if
    $
        integral_0^t W_(t -) Delta kappa_s dif bb(N)^a_s = - integral_0^t W_(t -) dif bb(N)^a_s 
    $
    and this is
    $
        bb(1) {tau^(g^*) <= t} W_(tau^(g^*) -) Delta kappa_(tau^(g^*)) = - bb(1) {tau^(g^*) <= t} W_(tau^(g^*) -)
    $
    By assumption, $W_(tau^(g^*) -) > 0$ (looking at the explicit solution of the SDE) and so the above holds if and only if
    $
        bb(1) {tau^(g^*) <= t} Delta kappa_(tau^(g^*)) = - bb(1) {tau^(g^*) <= t}
    $
    Taking $t -> oo$ gives the desired result. On the other hand, if the result holds then,
    $
        bb(1) {tau^(g^*) <= t} Delta kappa_(tau^(g^*)) &= bb(1) {tau^(g^*) <= t} bb(1) {tau^(g^*) < oo} Delta kappa_(tau^(g^*)) \
            &=bb(1) {tau^(g^*) <= t} bb(1) {tau^(g^*) < oo} (-1) = - bb(1) {tau^(g^*) <= t}
    $
] 

Now, we consider only $kappa$'s of the form 
$
    kappa (t) = integral_0^t sum_(x in cal(A)) bb(1) {s <= t} tilde(h) (s, x) M^(a, x) (dif s)
$
with $tilde(h) (s, x)$ $P$-$cal(F)_t$ predictable
with the restriction stated in the above theorem.
We make this restriction as any reasonable exchangeability conditions
should be placed on the treatment process.

#theorem[
    Let $kappa_t = integral_0^t sum_(x in cal(A)) bb(1) {s <= t} tilde(h) (s, x) M^(a, x) (dif s)$
    for some $P$-$cal(F)_t$-predictable process $tilde(h) (s, x)$
    and that $Q_kappa (tau^(g^*) = oo) = 1$.
    Suppose that $Delta kappa_t >= -1$ and $Delta kappa_t^* > -1$ if $t < tau^(g^*)$
    and that $cal(E) (kappa)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale.
    Suppose that $cal(A) = {a_0, a_1}$ and that $pi_t^* (a_1) = 1$.
    Then any $kappa$ with $tilde(h) (s, a_1)$ a $P$-$cal(F)_t$-predictable process and
    $
        tilde(h) (s, a_0) =bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s))
    $
    will satisfy the condition 2. of @thm:identifiabilitygeneral. Moreover, this solution is unique in the sense that
    whenever $integral_0^t tilde(h) (s, a_0) M^(a, a_0) (dif s)$ is of finite variation,
    this is equal to
    $
        integral_0^t bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s).
    $
    Conclude that, under regularity conditions,
    $
        cal(E) (kappa)_t &= 1 + integral_0^t cal(E) (kappa)_(s -) bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s) \ 
            &+ integral_0^t cal(E) (kappa)_(s -) tilde(h) (s, a_1) M^(a, a_1) (dif s)
    $
    are all the solutions to condition 2. of @thm:identifiabilitygeneral,
    where $tilde(h) (s, a_1)$ is any $P$-$cal(F)_t$-predictable process, ensuring that $cal(E) (kappa)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale.
]
#proof[

//We also suppose that $Delta Lambda^(a, x)_t < 1$.
//This happens for example if $Delta Lambda^a_t < 1$.
The above theorem gives that we must have
$
    Delta kappa_(tau^(g^*)) = sum_(x in cal(A)) tilde(h) (tau^(g^*), x) Delta M^(a, x)_(tau^(g^*)) = -1
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
]

= Score operator calculations

#theorem[
    Let $K_t^* = K_(t and tau^(g^*))$.
    1. The score operator $S: cal(M)^2 (P) -> cal(M)^2 (Q)$ is given by 
    $
        &Gamma mapsto Gamma - chevron.l Gamma, K^* chevron.r^P_(t) \
            &quad - integral_0^(t and tau^(g^*)) sum_(j=1)^K pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P).
    $
    2. Let
    $D: cal(M)^2 (P) -> cal(M)^2 (Q)$ be the linear operator defined by
    $
        Gamma mapsto Gamma - chevron.l Gamma, K^* chevron.r^P_(t).
    $
    Then its adjoint $D^*: cal(M)^2 (Q) -> cal(M)^2 (P)$ is given by
    $
        Gamma' mapsto Gamma^'_0 + integral_0^t W_(s-) dif (Gamma' + [Gamma', K^*])_s
    $
    The adjoint of the score operator $S^*: cal(M)^2 (Q) -> cal(M)^2 (P)$ is given by
    $
        Gamma' mapsto D^* Gamma' - integral_0^t bb(1) {tau^(g^*) <= s} sum_j sum_k pi_s^* ({a_j}) W_(s-) (dif chevron.l M^(a, a_j), Gamma' chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s.
    $
    or $("Id" - sum_j Y_j^*) (D^*)$ where $Y_j: cal(M)^2 (P) -> cal(M)^2 (P)$ is given by
    $
        Y_j Gamma = integral_0^(dot and tau^(g^*)) sum_k pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) chevron.r_s^P - pi_s ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) M^(a, a_j) (dif s)
    $
    and its adjoint $Y_j^*: cal(M)^2 (P) -> cal(M)^2 (P)$ is given by
    $
        Y_j^* Gamma = integral_0^t bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), Gamma' chevron.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s
    $
    3. $"ker"(S^*) = {0}$ if $pi_s ({a_j}) (P) > eta$ for all $s in [0, T]$ and $j$ for some $eta > 0$.
    4. $K^* in "ker"(S)$.
]

1. Let $macron(K)_t = K^*_t + bb(N)_t^a$
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
    chevron.l Gamma, M^(a, a_j) chevron.r_t^P &= (partial_epsilon (pi_t ({a_j}) (P_epsilon)) Lambda^(a) (dif t) (P) + pi_t ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_t^P)
$
so we conclude that
$
    partial_epsilon (pi_t ({a_j}) (P_epsilon)) &= (dif chevron.l Gamma, M^(a, a_j) chevron.r_t^P - pi_t ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_t^P) / (dif Lambda^(a) (t) (P)) \
        &= (dif chevron.l Gamma, (1-pi_dot ({a_j}) (P)) bullet M^(a, a_j) - pi_dot ({a_j}) (P) bullet sum_(i != j) M^(a, a_i) chevron.r_t^P) / (dif Lambda^(a) (t) (P)) \
$
Here, we have used that $partial_epsilon Lambda_t (P_epsilon) = chevron.l Gamma, M chevron.r_t^P$
if $M = N - Lambda (P)$.

$
    macron(K)_t &= integral_0^(t and tau^(g^*)) sum_(j=1)^K ((pi^*_(s) ({a_j}))/(pi_(s) ({a_j})) - 1) N^(a, a_j) (dif s) + bb(N)_t^a \
        &= integral_0^(t and tau^(g^*)) sum_(j=1)^K (1-pi^*_s ({a_j})) (-1) N^(a, a_j) (dif s) + bb(N)_t^a \
        &quad + integral_0^(t and tau^(g^*)) sum_(j=1)^K pi^*_s ({a_j}) ((1)/(pi_(s) ({a_j})) - 1) N^(a, a_j) (dif s) \
        &= integral_0^(t and tau^(g^*)) sum_(j=1)^K pi^*_s ({a_j}) ((1)/(pi_(s) ({a_j})) - 1) N^(a, a_j) (dif s) \
$ <eq:barKrep1>
This can also be written as
$
    macron(K)_t &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) ((1)/(pi_(s) ({a_j})) - 1) M^(a, a_j) (dif s) + bb(L)_t^a
$ <eq:barKrep2>
Calculating the derivative of @eq:barKrep2 gives
$
    partial_epsilon macron(K)_t^epsilon &= - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) \
        &quad - integral_0^(tau and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) ((1)/(pi_(s) ({a_j})) - 1) partial_epsilon (Lambda^(a, a_j) (dif s) (P_epsilon)) + partial_epsilon bb(L)_t^a (P_epsilon) \
        &=- integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) \
        &quad - integral_0^(tau and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) ((1)/(pi_(s) ({a_j})) - 1) dif chevron.l Gamma, M^(a, a_j) chevron.r^P_s + chevron.l Gamma, bb(L)^a chevron.r^P_t \
        &= -integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) - chevron.l Gamma, K^* chevron.r^P_(t),
$
again using that $partial_epsilon Lambda_t (P_epsilon) = chevron.l Gamma, M chevron.r_t^P$
if $M = N - Lambda (P)$ is a $P$-martingale.
However for @eq:barKrep1, we can also get that 
$
    partial_epsilon macron(K)_t^epsilon &= -integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) N^(a, a_j) (dif s) 
$
Also note that
$
    (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s) =  sum_(j=1)^K pi_s^* ({a_j}) (1-pi_(s) ({a_j})) Delta N^(a, a_j) (s)
$
by @eq:barKrep1.
Thus,
$
    sum_(0 < s <= t) (partial_epsilon Delta macron(K)_s^epsilon) (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s) &= - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) 1/(pi_s ({a_j}))^2 (1-pi_(s) ({a_j})) N^(a, a_j) (dif s) \
        &=- integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) N^(a, a_j) (dif s) \
            &= - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) M^(a, a_j) (dif s) \
        &quad - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) Lambda^(a, a_j) (dif s) 
$
Conclude that, if $pi_s ({a_j}) (P) > 0$ for all $s in [0, T]$ and $j$,
$
    &partial_epsilon macron(K)_t^epsilon - sum_(0 < s <= t) (partial_epsilon Delta macron(K)_s^epsilon) (Delta macron(K)^0_s) / (1 + Delta macron(K)^0_s) \
        &=- integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)^2) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s)  - chevron.l Gamma, K^* chevron.r^P_(t) \
        &quad + integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) M^(a, a_j) (dif s) \
        &quad + integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) Lambda^(a, a_j) (dif s) \
        &= - chevron.l Gamma, K^* chevron.r^P_(t) \
        &quad - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) M^(a, a_j) (dif s) \
        &quad + integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (1/(pi_(s) ({a_j}))-1) Lambda^(a, a_j) (dif s) \
        &= - chevron.l Gamma, K^* chevron.r^P_(t) \
            &quad - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1)/(pi_(s) ({a_j}) (P)) partial_epsilon (pi_(s) ({a_j}) (P_epsilon)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
            &= - chevron.l Gamma, K^* chevron.r^P_(t) \
            &quad  - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) chevron.r_t^P - pi_t ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) 
$ <eq:scoreoperatorfinal>
// Note that $(dif chevron.l Gamma, M^(a, a_j) chevron.r_t^P - pi_t ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_t^P) / (dif Lambda^(a, a_j) (t) (P))$
// can be be chosen predictable so that the corresponding term is a (local) martingale.

Conclude that the Score operator $S$ is given by
$
    cal(M)^2 (P) in.rev Gamma &mapsto Gamma - chevron.l Gamma, K^* chevron.r^P_(t) \
        &quad - integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) in cal(M)^2 (Q)
$ <eq:scoreoperator>

2. Assume that we have found the adjoint operator of $D : cal(M)^2 (P) -> cal(M)^2 (Q)$
$
    cal(M)^2 (P) in.rev Gamma &mapsto Gamma - chevron.l Gamma, K^* chevron.r^P_(t) in cal(M)^2 (Q) \
$
say $D^* : "Range"(D) subset cal(M)^2 (Q) -> cal(M)^2 (P)$.
Let $H_j: cal(M)^2 (P) -> cal(M)^2 (Q)$ be given by
$
    H_j Gamma = integral_0^(t and tau^(g^*))  pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) chevron.r_t^P - pi_t ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P)
$
Then, we have that

$
    chevron.l H_k Gamma, Gamma chevron.r_Q &:= mean(Q) [chevron.l H_k Gamma, Gamma' chevron.r^Q] \
        &= mean(Q) [chevron.l integral_0^(dot and tau^(g^*))  pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) chevron.r_s^P - pi_s ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) D M^(a, a_j) (dif s), Gamma' chevron.r^Q_s] \
        &= mean(Q) [chevron.l D integral_0^(dot and tau^(g^*))  pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) chevron.r_s^P - pi_s ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) M^(a, a_j) (dif s), Gamma' chevron.r^Q_s] \
        &= mean(P) [chevron.l integral_0^(dot and tau^(g^*))  pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) chevron.r_s^P - pi_s ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) M^(a, a_j) (dif s), D^* Gamma' chevron.r^P_s] \
        &:= mean(P) [chevron.l Y_j Gamma, D^* Gamma' chevron.r^P_s] \
        &= chevron.l Gamma, Y_j^* D^* Gamma' chevron.r_P,
$
so if we have found $D^*$ and $Y_j^*$, we have found the adjoint of $H_j$.
Here, we let
$Y_j : cal(M)^2 (P) -> cal(M)^2 (P)$ be given by
$
    Y_j Gamma = integral_0^(dot and tau^(g^*)) sum_k pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) chevron.r_s^P - pi_s ({a_j}) (P) dif chevron.l Gamma, M^(a) chevron.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) M^(a, a_j) (dif s)
$
Then, we may calculate directly that
$
    chevron.l Y_j Gamma, Gamma' chevron.r_P &:= mean(P) [chevron.l Y_j Gamma, Gamma' chevron.r^P] \
        &= mean(P) [chevron.l integral_0^(dot and tau^(g^*)) sum_k pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r^P_s) / (dif Lambda^(a, a_j) (s) (P)) dif M^(a, a_j) (s), Gamma' chevron.r^P] \
        &= mean(P) [chevron.l Gamma, bb(1) {tau^(g^*) <= dot} sum_k m_(dot,k,j)^* (dif chevron.l M^(a, a_j), Gamma' chevron.r_dot^P)/(dif Lambda^(a, a_j) (dot) (P)) bullet (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)) chevron.r^P] \
        &= mean(P) [chevron.l Gamma, Y_j^* Gamma' chevron.r^P]\
        &= chevron.l Gamma, Y_j^* Gamma' chevron.r_P,
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
    &integral_0^t bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), D^* Gamma' chevron.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &= integral_0^t bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) (dif chevron.l M^(a, a_j), Gamma' + [Gamma', K^*] chevron.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s
$

FACT:
$
    chevron.l X, Y chevron.r^Q = chevron.l X + [X, K^*], Y chevron.r^P = chevron.l X, Y + [Y, K^*] chevron.r^P,
$
so it follows that
$
    &integral_0^t bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) (dif chevron.l M^(a, a_j), Gamma' + [Gamma', K^*] chevron.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &= integral_0^t bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) (dif chevron.l M^(a, a_j), Gamma' chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s 
//        &= integral_0^t bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) (dif chevron.l M^(a, a_j), Gamma' chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (N^(a, a_j) - pi_dot ({a_j}) (P) bullet N^(a))_s.
$
Note that this operator sends to piecewise constant functions.
3.
Note that the adjoint operator can be written as $("Id" - sum_j Y_j^*) D^*$.
If $"Id" - sum_j Y_j^*$ is injective, it holds that
$
    "ker" (S^*) = "ker" (("Id" - sum_j Y_j^*) D^*) = "ker" (D^*) = {0}
$
where the last equality follows by "Projection Notes".
So this will follow, if we can show that $"Id" - sum_j Y_j^*$ is injective.
//Note that $"ker" ("Id" - sum_j Y_j^*) = "ran" ("Id" - sum_j Y_j)^perp$.
To this end, we shall show that $"Id" - sum_j Y_j$ has dense range in $cal(M)^2 (P)$ (Corollaries to Theorem 4.12 of Rudin, Functional Analysis, 2nd edition).

Take $Gamma^* in cal(M)^2 (P)$ such that
$
    Gamma^* = integral_0^dot sum_x gamma^*_x (s) M^(x) (dif s)
$
where $gamma^*_x (s)$ is bounded and predictable
We shall find $Gamma in cal(M)^2 (P)$ such that
$
    Gamma^* = Gamma - sum_j Y_j Gamma.
$
We will find our solution as 
$
    Gamma &= integral_0^dot sum_x gamma_x (s) M^(x) (dif s),
$
where $gamma_x (s)$ is bounded and predictable.
We now explain how this results in dense range:
The lemma on p. 173 of @protter2005stochastic shows that any
$Gamma^* in cal(M)^2 (P)$ can be approximated in $cal(M)^2 (P)$ by a sequence of such processes.

//We show that $sum_j Y_j^*$ is a contraction; this then follows
//by a fixed-point theorem.

//Another strategy: Show that $-(sum_j Y_j^* - "Id")$ is surjective.
//By Fredholms alternative, this will imply injectivity under certain regularity conditions. Alternatively,
//can try to show the same for $-(sum_j Y_j - "Id")$.

We will need to find the $chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_t^P$ term.
$
    chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_t^P &=  integral_0^(t) sum_x h_x (s) dif chevron.l M^(x), M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_s^P \
$
Now note that
$
    chevron.l M^(x), M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_s^P &= Lambda_s^(*,x,j) - integral_0^s Delta chevron.l M^x chevron.r_s dif Lambda^(a,a_j) (s) + integral_0^s pi_s ({a_j}) (P) Delta chevron.l M^x chevron.r_s dif Lambda^(a) (s) \
        &= Lambda_s^(*,x,a_j) - integral_0^s Delta chevron.l M^x chevron.r_s pi_s ({a_j}) (P) dif Lambda^(a) (s) + integral_0^s pi_s ({a_j}) (P) Delta chevron.l M^x chevron.r_s dif Lambda^(a) (s) \
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
    Y_j Gamma - Gamma &= integral_0^(dot and tau^(g^*)) sum_j sum_k pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r^P_s) / (dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) )_s - integral_0^dot sum_x gamma_x (s) M^(x) (dif s) \
        &= integral_0^(dot and tau^(g^*)) sum_j sum_k pi_s^* ({a_j}) sum_(x in cal(A)) gamma_x (s) (bb(1) {a_j= x} - pi_s ({x}) (P))dif M_s^(a, a_j) - integral_0^dot sum_x gamma_x (s) M^(x) (dif s) \
$
Whenever $x in.not cal(A)$, we can choose $gamma_x (s) = - gamma^*_x (s)$.
Otherwise, we may pick
$
    gamma_x (s) &= bb(1) {s <= tau^(g^*)} sum_k bb(1) {event(k-1) < s <= event(k)} bb(1) {x != g^*_k (history(k-1), s)} (- gamma^*_x (s)) \
        &+ bb(1) {s <= tau^(g^*)} sum_k bb(1) {event(k-1) < s <= event(k)} bb(1) {x = g^*_k (history(k-1), s)} (- (sum_(y in cal(A), y!= x) pi_s ({y}) (P) gamma^*_y (s)) / (pi_s ({x}) (P))) \
        &+ bb(1) {s > tau^(g^*)} (- gamma^*_x (s)).
$
which is bounded by assumption and predictable. 
// Now calculate
// $
//     S S^* Gamma &= (D - sum_j D Y_j)(D^* Gamma - sum_j Y_j^* D^* Gamma) \
//         &= D D^* Gamma - D sum_j Y_j^* D^* Gamma - sum_j D Y_j D^* Gamma + (sum_j D Y_j) sum_i Y_i^* D^* Gamma \
//         &= Gamma_0 + integral_0^dot macron(W)_s dif Gamma_s  - D sum_j Y_j^* D^* Gamma - (sum_j D Y_j) D^* Gamma + (sum_j D Y_j) (sum_i Y_i^* D^* Gamma) 
// $
// Note that
// $
//     (sum_j D Y_j) (sum_i Y_i^* D^* Gamma) &= sum_j sum_i D Y_j Y_i^* D^* Gamma \
//         &= sum_j sum_i integral_0^(dot and tau^(g^*)) sum_k pi_s^* ({a_j}) (dif chevron.l Y_i^* D^* Gamma, M^(a, a_j) - pi_s ({a_j}) (P) bullet M^(a)  chevron.r_s^P) / (dif Lambda^(a, a_j) (t) (P)) \
//         &times dif (M^(a, a_j) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
//         &= sum_j sum_i integral_0^(dot and tau^(g^*)) sum_k pi_s^* ({a_j}) \
//         &times (bb(1) {tau^(g^*) <= s} sum_k m_(s,k,i)^* W_(s-) (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif chevron.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a), M^(a, a_i) - pi_dot ({a_i}) (P) bullet M^(a) chevron.r_s) / (dif Lambda^(a, a_j) (t) (P)) \
//         &= sum_j integral_0^(dot and tau^(g^*)) W_(s-) sum_k pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) (dif chevron.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_s) / (dif Lambda^(a, a_j) (t) (P)) \
//         &times dif (M^(a, a_j) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
// $
// and
// $
//     D sum_j Y_j^* D^* Gamma &= D sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
//         &= sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (D (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)))_s \
//         &= sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) \
//         &times (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) - chevron.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a), K^* chevron.r^P)_s \
// $
// //         &= sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) \
// //         &times (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) - chevron.l M^(a, a_j), K^* chevron.r^P)_s \
// // $
// // Here, we use that
// // $
// //     chevron.l - pi_dot ({a_j}) (P) bullet M^(a), K^* chevron.r^P_t &= integral_0^(t and tau^(g^*)) sum_i (pi_s ({a_i}) - pi_s^* ({a_i}) dif chevron.l M^(a, a_j), M^(a, a_i) chevron.r_s^P \
// //         &= 0
// // $
// Finally, note that
// $
//     sum_j D Y_j D^* Gamma &= integral_0^(t and tau^(g^*)) W_(s-)  sum_(j=1)^K pi_s^* ({a_j}) (dif chevron.l Gamma + [Gamma, K^*], M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
//         & integral_0^(t and tau^(g^*)) W_(s-)  sum_(j=1)^K pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r_t^Q) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P)
// $
// Thus, we find
// $
//     S^* S Gamma &= sum_j integral_0^(dot and tau^(g^*)) W_(s-) sum_k pi_s^* ({a_j}) \
//         &quad times ((dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) ((dif chevron.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_s) / (dif Lambda^(a, a_j) (t) (P)) -1) - (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r_t^Q) / (dif Lambda^(a, a_j) (t) (P))) \
//         &quad times dif (M^(a, a_j) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
//         &+sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-) pi_s ({a_j}) (P)  (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a) - chevron.l M^(a), K^* chevron.r^P)_s \
//         &+ Gamma_0 + integral_0^dot macron(W)_s dif Gamma_s \
//     &= sum_j integral_0^(dot and tau^(g^*)) W_(s-) sum_k pi_s^* ({a_j}) \
//         &quad times ((dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) ((dif chevron.l M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r^P_s) / (dif Lambda^(a, a_j) (t) (P)) -1) - (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r_t^Q) / (dif Lambda^(a, a_j) (t) (P))) \
//         &quad times dif (M^(a, a_j) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
//         &+sum_j integral_0^(dot and tau^(g^*)) bb(1) {tau^(g^*) <= s} sum_k pi_s^* ({a_j}) W_(s-)  (dif chevron.l M^(a, a_j), Gamma chevron.r_s^Q)/(dif Lambda^(a) (s) (P)) dif (M^(a) - chevron.l M^(a), K^* chevron.r^P)_s \
//         &+ Gamma_0 + integral_0^dot macron(W)_s dif Gamma_s
// $

// With respect to the adjoint of the Score operator maybe conclude that
// the argument in Kjetils document shows that the adjoint gives
// my efficient influence function.'

4.

To this end, we will need to calculate $chevron.l K^* chevron.r^P_t$ and $chevron.l K^*, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_t^P$.

$
    chevron.l K^* chevron.r^P_t &= integral_0^(t and tau^(g^*)) sum_i sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)((pi_s^* ({a_i}))/(pi_s ({a_i})) - 1) dif chevron.l M^(a, a_i), M^(a, a_j) chevron.r_s^P \
        &= integral_0^(t and tau^(g^*)) sum_i sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)((pi_s^* ({a_i}))/(pi_s ({a_i})) - 1) (bb(1) {i=j}- Delta Lambda^(a,a_i)) dif Lambda^(a, a_j) (s) \
        &= integral_0^(t and tau^(g^*)) sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)^2 dif Lambda^(a, a_j) (s) \
        &quad - integral_0^(t and tau^(g^*)) sum_i sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)((pi_s^* ({a_i}))/(pi_s ({a_i})) - 1) Delta Lambda^(a,a_i) dif Lambda^(a, a_j) (s) \
        &= integral_0^(t and tau^(g^*)) sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)^2 dif Lambda^(a, a_j) (s) \
        &quad - integral_0^(t and tau^(g^*)) sum_i sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)((pi_s^* ({a_i}))/(pi_s ({a_i})) - 1) pi_s ({a_i}) pi_s ({a_j}) Delta Lambda^(a) (s) dif Lambda^(a) (s) \
        &= integral_0^(t and tau^(g^*)) sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)^2 dif Lambda^(a, a_j) (s) \
        &quad - integral_0^(t and tau^(g^*)) sum_i sum_j ( pi^*_s ({a_j})- pi_s ({a_j}) )(pi_s^* ({a_i}) - pi_s ({a_i}))  Delta Lambda^(a) (s) dif Lambda^(a) (s) \
        &=integral_0^(t and tau^(g^*)) sum_j ( (pi^*_s ({a_j})) / (pi_s ({a_j})) - 1)^2 dif Lambda^(a, a_j) (s) \
        &= integral_0^(t and tau^(g^*)) sum_j  (pi^*_s ({a_j})) / (pi_s ({a_j})) dif Lambda^(a) (s) - 2 integral_0^(t and tau^(g^*)) sum_j  (pi^*_s ({a_j})) dif Lambda^(a) (s) + integral_0^(t and tau^(g^*)) sum_j pi_s ({a_j}) (P) dif Lambda^(a) (s) \
        &= integral_0^(t and tau^(g^*)) (sum_j  (pi^*_s ({a_j})) / (pi_s ({a_j})) -1)dif Lambda^(a) (s).
$
For the next calculation, we have that
$
    chevron.l K^*, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_t^P &= integral_0^(t and tau^(g^*)) sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  dif chevron.l M^(a, a_i), M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a) chevron.r_s^P \
        &= integral_0^(t and tau^(g^*)) sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  (bb(1) {i=j}- pi_s ({a_i}) (P)) dif Lambda^(a, a_j) (s).
$
by the previous calculations. Therefore, it holds that
$
    &integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (dif chevron.l Gamma, M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a)  chevron.r_t^P) / (dif Lambda^(a, a_j) (t) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
        &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j})  sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  (bb(1) {i=j}- pi_s ({a_i}) (P)) (M^(a, a_j) (dif s) - dif chevron.l M^(a, a_j), K^* chevron.r_s^P) \
        &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j})  sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  (bb(1) {i=j}- pi_s ({a_i}) (P)) \
        &quad times (M^(a, a_j) (dif s) - (sum_v (pi^*_s ({a_v})) / (pi_s ({a_v})) - 1) dif chevron.l M^(a, a_j), M^(a, v) chevron.r_s^P) \
        &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j})  sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  (bb(1) {i=j}- pi_s ({a_i}) (P)) \
        &quad times (M^(a, a_j) (dif s) - (sum_v (pi^*_s ({a_v})) / (pi_s ({a_v})) - 1) pi_(s) ({a_v}) (bb(1) {j=v}- pi ({a_j} Delta Lambda^(a)) dif Lambda^(a) (s))) \
        &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j})  sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  (bb(1) {i=j}- pi_s ({a_i}) (P)) \
        &quad times (M^(a, a_j) (dif s) - (sum_v (pi^*_s ({a_v})) / (pi_s ({a_v})) - 1) pi_(s) ({a_v}) bb(1) {j=v} dif Lambda^(a) (s)) \
        &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j})  sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  (bb(1) {i=j}- pi_s ({a_i}) (P)) \
        &quad times (M^(a, a_j) (dif s) - ((pi^*_s ({a_j})) / (pi_s ({a_j})) - 1) pi_(s) ({a_j}) dif Lambda^(a) (s)) \
    &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j})  sum_i ( (pi^*_s ({a_i})) / (pi_s ({a_i})) - 1)  (bb(1) {i=j}- pi_s ({a_i}) (P)) \
        &quad times (M^(a, a_j) (dif s) - (pi^*_s ({a_j}) - pi_(s) ({a_j}))  dif Lambda^(a) (s)) \
     &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) (1) / (pi_s ({a_j}))  (1- pi_s ({a_i}) (P)) \
        &quad times (N^(a, a_j) (dif s) - pi^*_s ({a_j})  dif Lambda^(a) (s)) \
        &- integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j})  sum_i  (bb(1) {i=j}- pi_s ({a_i}) (P)) \
        &quad times (N^(a, a_j) (dif s) - pi^*_s ({a_j})  dif Lambda^(a) (s)) \
        &= integral_0^(t and tau^(g^*))  sum_(j=1)^K pi_s^* ({a_j}) ((1) / (pi_s ({a_j})) - 1) (N^(a, a_j) (dif s) - 1)  dif Lambda^(a) (s))
$
This we find the score operator is given by evaluated at $K^*$ by combining the results, 
$
    - integral_0^(t and tau^(g^*))  sum_(j=1)^K bb(1) {event(k-1) < s <= event(k)} bb(1) {j != g^*_k (history(k-1), s)} N^(a, a_j) (dif s) \
$
which is zero $Q$-a.s.

== Efficient influence function calculations

Let $I_P nu (tilde(Y))$ be an influence function for $nu: cal(P)_(|sigma(tilde(Y))) -> R$,
$nu (P) = E_P [tilde(Y)]$ and let us take $I_P nu (tilde(Y)) = tilde(Y) - E_P [tilde(Y)]$.
Let $zeta_t = mean(P) [I_P nu (Y) | cal(F)_t] = mean(P) [tilde(Y) | cal(F)_t] - E_P [tilde(Y)]$.
Now, we see that

$
    S^* zeta_T &= W_T (P) (Y_T - mean(P) [tilde(Y)_T]) \
        &- integral_0^(T) zeta_(s -) W (s -) dif K^*_s \
        &- integral_0^T bb(1) {s <= tau^(g^*)} sum_j pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), mean(P) [W_T (P) Y_T | cal(F)_(dot)] -  E_P [tilde(Y)] chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &= W_T (P) Y_T - (W_T (P) - integral_0^(T) W (s -) dif K^*_s) mean(P) [tilde(Y)_T]  \
        &- integral_0^(T) mean(Q) [Y_T | cal(F)_(s-)] W (s -) dif K^*_s \
        &- integral_0^T bb(1) {s<=tau^(g^*)} sum_j pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), mean(P) [W_T (P) Y_T | cal(F)_(dot)] chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
    &= W_T (P) Y_T - mean(P) [tilde(Y)_T]  \
        &- integral_0^(T) mean(Q) [Y_T | cal(F)_(s)] W (s -) dif K^*_s \
        &+ [mean(Q) [Y_T | cal(F)_(dot)], K^*]_T \
    &- integral_0^T bb(1) {s<=tau^(g^*)} sum_j pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), mean(P) [W_T (P) Y_T | cal(F)_(dot)] chevron.r_s^Q)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &= W_T (P) Y_T - mean(P) [tilde(Y)_T]  \
        &- integral_0^(T) mean(Q) [Y_T | cal(F)_(s)] W (s -) dif K^*_s \
        &+ integral_0^T sum_(j=1)^K ((pi_s^* ({a_j}))/(pi_s ({a_j})) -1) dif [mean(P) [W_T Y_T | cal(F)_(dot)], M^(a,a_j)]_s \
        &- integral_0^T bb(1) {s<=tau^(g^*)} sum_j pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), mean(P) [W_T (P) Y_T | cal(F)_(dot)] chevron.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \
        &- integral_0^T bb(1) {s<=tau^(g^*)} sum_j pi_s^* ({a_j}) (dif chevron.l M^(a, a_j), [mean(P) [W_T (P) Y_T | cal(F)_(dot)], K^*]  chevron.r_s^P)/(dif Lambda^(a, a_j) (s) (P)) dif (M^(a, a_j) - pi_dot ({a_j}) (P) bullet M^(a))_s \

$

The integrators can be replaced with their corresponding martingales.

@sequentialRegressionOhlendorff suggested the EIF:
$
    &W_T (P) Y_T - E_P [tilde(Y)_T] \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] sum_j (pi_s^* ({a_j})) / (pi_s ({a_j}))   N^(a,a_j) (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)^g_(s)] N^a (dif s) \
        &=  W_T (P) Y_T - E_P [tilde(Y)_T] \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] sum_j (pi_s^* ({a_j})) / (pi_s ({a_j}))   N^(a,a_j) (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)^g_(s)] N^a (dif s) \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] N^ell (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] N^ell (dif s) \
        &=  - E_P [tilde(Y)_T] \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] sum_j (pi_s^* ({a_j})) / (pi_s ({a_j}))   N^(a,a_j) (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)^g_(s)] N^a (dif s) \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] N^ell (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] N^ell (dif s) \
        &+ integral_0^T W(s -) N^y (dif s) \
        &= mean(Q) [Y_t | cal(F)_0] - E_P [tilde(Y)_T] \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] sum_j (pi_s^* ({a_j})) / (pi_s ({a_j}))   N^(a,a_j) (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)^g_(s)] N^a (dif s) \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] N^ell (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] N^ell (dif s) \
        &+ integral_0^T W(s -) N^y (dif s) - mean(Q) [Y_t | cal(F)_0] 
$
The latter function is a rewriting of the one in @sequentialRegressionOhlendorff,
while the first is suggested by projecting onto the propensity tangent space. 
Here, $cal(F)_s^g$ denotes the natural filtration, generated by observed data
with the treatment decisions specified by the treatment regime $g^*$.

We can write
$
    &-integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] sum_j (pi_s^* ({a_j})) / (pi_s ({a_j}))   N^(a,a_j) (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)^g_(s)] N^a (dif s) \
        &= -integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] sum_j ((pi_s^* ({a_j})) / (pi_s ({a_j})) - 1)   N^(a,a_j) (dif s) + integral_0^T W(s -) mean(Q) [Y_T | cal(F)^g_(s)] N^a (dif s) \
        &- integral_0^T W(s -) mean(Q) [Y_T | cal(F)_(s)] N^a (dif s)
$

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


#bibliography("references/ref.bib",style: "apa")


