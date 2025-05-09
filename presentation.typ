#import "@preview/colorful-boxes:1.4.3": *
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
///#import "@preview/cetz:0.3.3"
#import "@preview/cheq:0.2.2": checklist

#show: checklist
#set cite(form: "prose")
#show ref: it => [#text(fill: blue)[#it]]
#show math.equation: set text(9pt)
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

= Notation and target parameter
- Observe the jump process $Z(t) = (N^a (t), A (t), N ^ell (t), L(t), N^y (t), N^d (t))$ and contain the information in the filtration $(cal(F)_t)_(t >=0)$.
- $A(t) in {0, 1}$ and $L(t) in cal(L) subset.eq RR^d$ with $cal(L)$ finite. 
- In the time interval $[0, tauend]$ there are at most $K - 1$ changes of treatment and
covariates in total for a single individual.
- Thus, $cal(D)_n = history(K) = (event(K), status(K), event(K-1), status(K-1), treat(K-1), covariate(K-1), dots, treat(0), covariate(0)) ~ P in cal(M)$,
  where $history(k) = (event(k), status(k), treat(k), covariate(k), dots, treat(0), covariate(0))$.
- The counting processes $N^a$, $N^ell$, $N^y$, $N^d$, and $N^c$ have with probability 1 no jump times in common ($=>$ orthogonal martingales).
- Let $hazard(x, t, k)$ be the cause-specific hazard of the $k$'th event, $densitytrt(t, k)$ be
  the probability of treatment given $status(k)=a$, $event(k)=t$, and $history(k-1)$,
  amd $densitycov(t, dot, k)$ be the distribution of covariate given $status(k)=a$, $event(k)=t$, and $history(k-1)$.
#colorbox(
  title: "⚠️ Conditional distributions",
  color: "red",
  radius: 2pt,
  width: auto,
)[
    We assume that the conditional distributions $P(event(k) in dot | history(k-1)) lt.double m$ $P$-a.s., where $m$ is the Lebesgue measure on $RR_+$.
]

- Our overall goal is to estimate the interventional cumulative incidence function at time $tau$,
  $
      Psi_tau^g (P) = mean(P) [tilde(N)^y_tau],
  $
      had the treatment protocol $g$ been followed (adhering to treatment).
      
= Identifiability (no censoring)

We can also give a martingale argument in the lines of @ryalenPotentialOutcomes.
Let $Lambda^a_t (A) = pi_t ({a} | cal(F)_(t-)) Lambda^a_t$ be the compensator of $N_t (A)$ - the corresponding random measure of the treatment process, i.e.,
$
    N_t (A) = sum_(j=1)^K bb(1) {event(j) <= t, status(j) = a, treat(j) in A}
$ <eq:randommeasure>

#colorbox(
  title: "Identifiability",
  color: "green",
  radius: 2pt,
  width: auto,
)[
- *Consistency*: $tilde(N)^y_t bb(1) {T^a > t} = N^y_t bb(1) {T^a > t}$,
  where $T^a = inf {t >= 0 | A (t) = 0}$.
- *Exchangeability*: 
  The $P$-$cal(F)_t$  compensator for $N^a$ $Lambda^a_t (dot)$ is also the $P$-$cal(F)_t or sigma(tilde(N)^y)$ compensator
      and
  $
       &tilde(N)^y_t 
       perp treat(0) | covariate(0)
  $
- *Positivity*: The martingale $W (t) = product_(k=1)^(N_t) ((bb(1) {treat(k) = 1}) / (densitytrt(event(k), k)))^(bb(1) {status(k) = a}) (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0)))$ is uniformly integrable.

Then the estimand of interest is identifiable by
$
    Psi_(t)^g (P) = bb(E)_P [tilde(N)^y_t] = bb(E)_P [N^y_t W (t)].
$
]

#proof[
    First note that by (2.7.7) of @andersenStatisticalModelsBased1993, we have
    $bold(tilde(Lambda)) = (0, Lambda^(a), Lambda^(ell 1), dots, Lambda^(ell d), Lambda^y, Lambda^d)$
    and $bold(Lambda) (t) = (Lambda^a (t) pi (0 | cal(F)_(t-)), Lambda^(a) (t) pi (1 | cal(F)_(t-)), Lambda^(ell 1) (t), dots, Lambda^(ell d) (t), Lambda^y (t), Lambda^d (t))$,
we can simply write
$
    W (t) = (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0)))  (product_(s in (0, t]) product_h (d tilde(Lambda)_h (s))^(Delta N_h (s)) (1- d tilde(Lambda)_bullet (s))^(1 - Delta N_bullet (s))) / ( product_(s in (0, t]) product_h (d Lambda_h (s))^(Delta N_h (s)) (1- d Lambda_bullet (s))^(1 - Delta N_bullet (s))) \
$
Then (2.7.8) of @andersenStatisticalModelsBased1993 simply states that $W$ is
the unique solution of the equation
$
    W (t) = (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0))) + integral_0^t W(s -) (1/( pi_s (1 | cal(F)_(s-))) - 1) d M_s^a ({1}) - integral_0^t W (s-) d M_s^a ({0})
$
Under consistency (and regularity conditions for the integrands),
$
    mean(P) [W (t) N_t^y] &= mean(P) [tilde(N)_t^y W (t)] \
        &=mean(P) [tilde(N)_t^y  (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0)))] + mean(P) [integral_0^t tilde(N)_t^y W (s-) (1/( pi_s (1 | cal(F)_(s-))) - 1) d M_s^a ({1})] - mean(P) [integral_0^t tilde(N)_t^y W (s-) d M_s^a ({0})] \
        &=mean(P) [tilde(N)_t^y  (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0)))] + 0 - 0 \
        &=mean(P) [tilde(N)_t^y].
$
In the third equality, we use the fact that the integrands under exchangeability are predictable, and hence the integrals are zero mean martingales.
In the last equality, we simply use the baseline exchangeability condition.
]
//- weight not uniquely determined?

//The condition for exchangeability may be problematic
//(the expectation in the proof can be written as a product of a conditional expecatations, the first conditioning on $event(k) <= tau <= event(k+1)$; the second one
//is the expectation but without the potential outcomes; so one typical requirement will be that the events do not depend on the treatment ...).
 
// Alternatively, we can posit the existence of potential outcomes $tilde(N)^y_(k,tau)$ of $bb(1) {event(k) <= tau, status(k) = y}$ so that
// $
// tilde(N)^y_tau = sum_(k=1)^K tilde(N)^y_(k,tau)
// $

// #colorbox(
//   title: "Alternative condition for exchangeability and consistency",
//   color: "blue",
//   radius: 2pt,
//   width: auto,
// )[
// - *Sequential consistency*: $tilde(N)^y_(k,tau) bb(1) {T^a > tau} = N^y_(k,tau) bb(1) {T^a > tau}$, for $k = 1, dots, K$.
// - *Exchangeability*: We have
//   $
//        &tilde(N)^y_(j,tau)
//        perp treat(k) | history(k-1), event(k), status(k) = a, quad forall j>k>0, \
//        &tilde(N)^y_(j,tau)
//        perp treat(0) | covariate(0), quad forall j>0.
//   $
   
// 


Two main recursive identification formulas:

#colorbox(
  title: "Identification formulas",
  color: "red",
  radius: 2pt,
  width: auto,
)[
    Let $Qbar(K) = bb(1) {event(K) <= tau, status(K) = y}$ and define inductively, 
    $
        Qbar(k-1)&= mean(P) [bb(1) {event(k) <= tau, status(k) = ell) Qbar(k) (treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
            &qquad+ bb(1) {event(k) <= tau, status(k) = a) Qbar(k) (1, covariate(k-1), event(k), status(k), history(k-1)) \
            &qquad+ bb(1) {event(k) <= tau, status(k) = y) mid(|) history(k-1)] \
            &= p_(k a) (t | history(k-1))  + p_(k ell) (t | history(k-1)) + p_(k y) (t | history(k-1)) \
    $
    for $k = K-1, dots, 1$ with
    $
        p_(k a) (t | history(k-1)) = integral_(event(k-1))^t S_k (s- | history(k-1)) Qbar(k+1) (1, covariate(k-1), s, a, history(k-1)) Lambda_k^a (dif s | history(k-1))
    $
    and
    $
        &p_(k ell) (t | history(k-1)) = integral_(event(k-1))^t S_k (s- | history(k-1)) \
            &qquad (mean(P) [Qbar(k+1) (treat(k-1), covariate(k), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] ) Lambda_k^ell (dif s | history(k-1))
    $
    and
    $
            p_(k y) (t | event(k-1)) = integral_(history(k-1))^t S_k (s- | history(k-1)) Lambda_k^y (dif s | history(k-1))
    $
    Then, $Psi_tau^g (P) = mean(P) [Qbar(0) (1, covariate(0))]$.
]
- Notably the iterative representation using the $p$-functions is computationally intensive,
  and the resulting integral is high dimensional. We may therefore want to use Bayesian/Monte Carlo methods for 
  the high-dimensional integral, but this is not the focus of this work.

= Censoring
- We assume there exists a censoring time $C>0$ with $N^c (t) = bb(1) {C <= t}$, so
  that we fully observe the process $(Z (t and C))_t$ and $(N^c (t and T^e))_t$, where $T^e$ denotes
  the terminal event time. Let $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$
  be the observed event times and $S^c$ the censoring survival function.
- Let $N^(r,x)$ be a random measures corresponding to the jump times of $Z$ and $N^c$ for the component $x$
  for the full data filtration $cal(F)^"full"_t = cal(F)_t or sigma (N^c (s) | s <= t)$, e.g., @eq:randommeasure.

== ICE-IPCW
#colorbox(
  title: "ICE-IPCW",
  color: "red",
  radius: 2pt,
  width: auto,
)[
    Assume that the intensity processes of $N^(r,x), x= a,ell,d,y$ with respect to the filtration
    $cal(F)_t$ are also the intensities with respect to the filtration
    $cal(F)^"full"_t$. Additionally, assume also that the intensity process of $N^c (t)$ with respect to the filtration
    $cal(G)_t$ is also the intensity process with respect to the filtration
    $cal(F)^"full"_t$.
    Then, we have that
    #math.equation(block: true, numbering: "(1)")[$
        Qbar(k-1) &= mean(P) [(bb(1) {eventcensored(k) <= tau, statuscensored(k) = ell})/( S_k^c (eventcensored(k-1) - | historycensored(k-1)) ) Qbar(k)(treatcensored(k-1), covariatecensored(k), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) <= tau, statuscensored(k) = a}) /(S_k^c (eventcensored(k-1) - | historycensored(k-1)))  Qbar(k) (1, covariatecensored(k-1), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) <= tau, statuscensored(k) = y}) /(S_k^c (eventcensored(k-1) - | historycensored(k-1))) mid(|) historycensored(k-1)]
    $] <eq:ipcw>
    for $k = K-1, dots, 1$. 
    Then, 
    $
        Psi_tau lr((Q)) = mean(P) [  Qbar(0) (1, covariate(0))].
    $
]
// #proof("sketch")[
//     Need to argue that the observed data
//     densities for $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$ are the same as
//     the full data densities for $(event(k), status(k), treat(k), covariate(k))$.
//     We can derive the compensator for the random measures with respect to the observed data filtration
//     in two ways. By a martingale argument and by there existing a compensator written in terms
//     of the hazards of $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$.
//     Since the compensator is unique, the theorem follows. 
// ]

The representation is nice,
1. it is useful for (locally) efficient inference. 
2. we do not use reweighting with the treatment propensity scores $=>$ increased stability/robustness.

= EIF/Debiased ML
- Want to do efficient estimation of our target functional $Psi_tau^g (P)$.

#colorbox(
  title: "Efficient influence function",
  color: "blue",
  radius: 2pt,
  width: auto,
)[
    Let
    $
        "MG"_k &= integral_(event(k - 1))^(tau and event(k)) (Qbar(k-1) (tau  | history(k-1))-Qbar(k-1) (u  | history(k-1))) 1/(S^c (u- | history(k-1)) S (u | history(k-1))) M_k^c (upright(d) u), \ 
        M_k^c (t) &= bb(1) {event(k-1) < t <= event(k)} (N^c (t) - Lambda^c (t | history(k-1))), \
        macron(Z)^a_(k,tau) (s) &= (bb(1) {event(k) <= s, status(k) = ell})/(S^c (event(k) - | history(k-1))) Qbar(k)(treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
            &quad + (bb(1) {event(k) <= s, status(k) = a})/(S^c (event(k) - | history(k-1))) Qbar(k)(1, covariate(k-1), event(k), status(k), history(k-1)) \
            &quad +  (bb(1) {event(k) <= s, status(k) = y})/(S^c (event(k) - | history(k-1) )), s < tau\
    $
    and $Qbar(k-1) (s | history(k-1)) &= mean(P) [macron(Z)^a_(k,tau) (s) | history(k-1)], s < tau$.
    The efficient influence function is given by
    #text(size: 7.5pt)[$
        phi_tau^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treat(j) = 1}) / (densitytrt(event(j), j)))^(bb(1) {status(j) = a}) \
            &qquad times 1/( product_(j=1)^(k-1) S^c (event(j)- | history(j-1))) bb(1) {status(k-1) in {ell, a}, event(k-1) < tau} (macron(Z)^a_(k,tau)- Qbar(k-1) + "MG"_k )\
                &quad quad +  Qbar(0) - Psi_tau (P),
    $]
] 

Estimating the martingale term is evidently computationally difficult.
A naive strategy is to apply the ICE-IPCW procedure for a sequence of time points.
However,
we can use the given ICE-IPCW estimator from the previous step $hat(nu)_(k)$ to provide a new
computationally feasible estimator for $Qbar(k+1) (s)$ used in $"MG"_k$.
First obtain the estimates $tilde(nu)_(k,tau)$ by regressing $macron(Z)^a_(k+1, tau) (hat(S^c), hat(nu)_(k+1,tau))$ on $(event(k), status(k), treat(k), history(k-1))$.
Now determine estimates on a fine grid $0 < s_1 < dots < s_(k(event(k-1))) < h_"max"$,

$
    hat(nu)^*_(k,tau) (s | history(k)) &= integral_(0)^(s-event(k)) product_(s in (0, u - event(k))) (1-sum_(x=a,l,d,y) hat(Lambda)_(k+1)^x (d s | history(k)))
           [hat(Lambda)_(k+1)^y (d u | history(k)) \
               &+ tilde(nu)_(k+1,tau) (u + event(k), a, 1, history(k)) hat(Lambda)_(k+1)^a (d u |  history(k)) \
        &+ tilde(nu)_(k+1,tau) (u + event(k), ell, treat(k), history(k)) hat(Lambda)_(k+1)^ell (d u |  history(k))]
$
for $s = event(k-1) + s_i$. Then,  we can estimate the EIF  by
$
    phi^* (hat(P)_n^*) &= (bb(1) {treat(0) = 1})/ (hat(pi)_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treat(j) = 1}) / (hat(pi) (event(j), treat(j), history(j-1))))^(bb(1) {status(j) = a}) 1/( product_(j=1)^(k-1) hat(S)^c (event(j)- | history(j-1))) bb(1) {status(k-1) in {ell, a}, event(k-1) < tau}  \
        & times (macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k,tau))- hat(nu)_(k-1, tau) (history(k-1)) + hat("MC")_k (hat(Lambda)_k^c, hat(nu)^*_(k,tau))) \
        & +  hat(nu)_(0, tau) (1, covariate(0)) - bb(P)_n hat(nu)_(0, tau) (1, dot)
$

To perform double/debiased machine learning, we need to find the
remainder term $R_2 (tilde(P), P, P_0)$ and
show that it has the typical product structure.

We cannot use the one in @rytgaardContinuoustimeTargetedMinimum2022,
because 1. theirs is without competing risks
and 2. they facilitate estimation in a different way.
This is because we end up estimating $Qbar(k+1) (tau)$
in two different ways.

#colorbox(
  title: "Remainder term",
  color: "blue",
  radius: 2pt,
  width: auto,
)[
    The remainder term $R_2 (tilde(P), P, P_0) = Psi_tau (P) - Psi_tau (P_0) + mean(P_0) [phi^* (tilde(P), P)]$ is given by
    $
        R_2 (tilde(P), P, P_0) &= sum_(k=1)^K integral bb(1) {t_1 < dots < t_(k) < tau} 
        product_(j = 0)^(k-2) ((pi_(0,j) (t_k, f^(bold(1))_(j-1))) / (pi_(j) (t_k, f_(j-1)^(bold(1)))))^(bb(1) {d_j = a}) \
            & qquad (product_(j=1)^(k-1) S_0^c (t_j- | f^(bold(1))_(j-1)))/( product_(j=1)^(k-1) S^c (t_j- | f_(j-1)^(bold(1)))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} z_k (f^(bold(1))_(k)) P_(cal(F)_(T_(k))) (d f_(k)),
    $
    Here $tilde(P), P$ means that we plug in two different estimators as described earlier ($nu_(k,tau)$ and $nu^*_(k,tau)$),
    and
    $
        z_k (history(k)) &= (((pi_(k-1,0) (event(k), history(k-1)))/ (pi_(k-1) (event(k), history(k-1))))^(bb(1) {status(k) = a})-1) (Qbar(k-1) (history(k-1))- nu_(k-1, tau) (history(k-1))) \
            &quad+((pi_(k-1,0) (event(k), history(k-1)))/ (pi_(k-1) (event(k), history(k-1))))^(bb(1) {status(k) = a}) \
            &qquad times integral_(event(k - 1))^(tau) ((S_0^c (u | history(k-1))) / (S^c (u | history(k-1)))-1) (nu^*_(k-1, tau) (d u |history(k-1)) - Qbar(k-1) (d u | history(k-1))) \
            &quad+((pi_(k-1,0) (event(k), history(k-1)))/ (pi_(k-1) (event(k), history(k-1))))^(bb(1) {status(k) = a}) integral_(event(k - 1))^(tau) V_k (u, history(k-1)) nu^*_(k-1, tau) (d u |history(k-1)),
    $
    and $V_k (u, history(k)) = integral_(event(k-1))^u ((S_0 (s | history(k-1))) / (S (s | history(k-1))) - 1)  (S_0^c (s- | history(k-1)))/(S^c (s- | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1)))$.
    Here $f^(bold(1))_(j)$ simply means that we insert 1 into every place where we have $a_i, i = 1, dots, j$ in $f_(j)$.
]

= Simulation + data application

???

#bibliography("references/ref.bib",style: "apa")
