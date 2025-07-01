#import "definitions.typ": *
#import "@preview/colorful-boxes:1.4.3": *
#set heading(numbering: "1")
#let example = thmplain("example", "Example").with(numbering: none)
#set math.equation(numbering: "(1)")

#show: thmrules.with(qed-symbol: $square$)

= Simulating longitudinal data for time-to-event analysis in continuous time

We simulate a cohort of patients who initiate treatment at time $t = 0$, denoted by $A(0) = 1$
and who are initially stroke-free, $L(0) = 0$.
All individuals are followed for up to $tauend = 900 "days"$ or until death.
Initially, we do not consider censoring or competing events. 
During follow-up, patients may experience (at most) one stroke, stop treatment (irreversibly), and die,
that is $N^x (t) <= 1$ for $x = a, ell, y$.
With these assumptions $K=2$ in the main note (at most two non-terminal events).
The primary outcome is the _risk of death within $tau = 720$ days_.

Our observations consist of
$
    O = (event(3), status(3), treat(2), covariate(2), event(2), status(2), treat(1), covariate(1), event(1), status(1), treat(0), covariate(0), "age"),
$
where $event(k)$ is the time of the $k$'th event, $status(k) in {ell, a, y}$ (stroke, visit, death),
$treat(k)$ is the treatment status at time $event(k)$, and $covariate(k)$ is the value of the covariate at time $event(k)$.
Note that we let $event(k) = oo$ if the $k$'th event cannot happen (because the previous event was a terminal event or the end of the study period was reached)
or if the $k$'th event occurs after the end of the study period.
Let Exp($lambda$) denote the exponential distribution with rate $lambda >= 0$.
We let $lambda = 0$ correspond to the case that the event cannot happen, i.e., $T_((1))^x = oo$.

Then, we generate the baseline variables as follows
$
    &"age" tilde "Unif"(40,90), \
        &L = 0, \
        & treat(0) = 1,
$

Now we describe the simulation mechanism corresponding to the first event that can happen.
We define $T_((1))^a$ such that the patient can be expected
to go to the doctor within the first year,
if the two other events have not occurred first.
As the first event, we draw
$
    &T_((1))^x  tilde "Exp"(lambda^x_1 exp(beta^x_(1,"age") "age"+ beta^x_(1,"A") treat(1) + beta^x_(1, "L") covariate(1))), x = ell, y \
        &T_((1))^a tilde 1 + cal(N)(0, delta) \
        &status(1) = "argmin"_(x = a, ell, y) T_((1))^x \
        &event(1) = T_((1))^status(1) \
        &treat(1) | event(1) = t, "age" = x cases(tilde "Bernoulli(expit"(alpha_(10) + alpha_(1, "age") x) "if" status(1) = a, 1 "otherwise") \
        &covariate(1) = 1, \
$
Note that we simulate from a "competing event setup" by defining latent variables $T_((1))^x$ for each possible event type $x$.

We now describe the second event that can happen.
If the first event was a terminal event -- either outcome or that the previous event happened after the end of the study period --
we stop and do not generate more data for this patient.
Now, we let $S_((2))$ denote the time between $event(1)$ and the second event $event(2)$,
i.e., $S_((2)) = event(2) - event(1)$.
As we required that $N^x (t) <= 1$,
if the first event was a stroke, we cannot have a second stroke,
and if the first event was a visit, we cannot have a second visit.
If the first event was a stroke, the doctor visit is likely to happen soon after,
so we simulate the corresponding latent time as an exponential random variable.
We will then generate the second event time $event(2)$ as follows:

$
    &S_((2))^ell tilde "Exp"(lambda^ell_2 exp(beta^ell_(2,"age") "age" + beta^ell_(2, A) treat(1)) bb(1) {status(1) = a}) \
        &S_((2))^y tilde "Exp"(lambda^y_2 exp(beta^y_(2,"age") "age" + beta^y_(2, A) treat(1) + beta^ell_(2, L) covariate(1))) \ 
        &S_((2))^a tilde "Exp"(gamma_0 exp(gamma_"age" "age") bb(1) {status(1) =ell}) \
            &status(2) = "argmin"_(x = a, ell, y,) S_((2))^x \
            &event(2) = event(1) + S_((2))^status(2) \
        &treat(2) | event(2) = t, "age" = x, treat(1) = a_1, covariate(1) = l_1 \
        &qquad =cases(tilde "Bernoulli(expit"(alpha_(20) + alpha_(2, "age") x + alpha_(2, "L") l_1)")" "if" status(2) = a, 1 "otherwise") \
        &covariate(2) = 1. \
$

Finally, we let $event(3) = S_((3)) + event(2)$ denote the time of the third event,
if it can happen.
We define the time $S_((3))$ as follows:
$
    S_((3))^y tilde "Exp"(lambda^y_3 exp(beta^y_(3,"age") "age" + beta^y_(3, A) treat(2) + beta^y_(3, L) covariate(2))) \
    status(3) = y \
    event(3) = event(2) + S_((3))^status(3).
$
Here, we furthermore make the assumption that
it does not matter whether the patient had a stroke first
and then visited the doctor, or visited the doctor first and then had a stroke.
Also, we assumed that the previous event times have no influence on anything,
only the "marks". However, this may be unrealistic, as the effect of a stroke on mortality may naturally decrease over time.

When the static intervention is applied, we put $treat(k) = 1$ for each $k = 1, dots, K$.
Some explanation for this is (probably) warranted.
//It is not too difficult to see that the likelihood factorizes as in #cite(<rytgaardContinuoustimeTargetedMinimum2022>, form: "prose")
//corresponding to the intervention that we are interested in (see e.g., Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose")).

= Plain Language Summary (for Clinical Audience)

We simulate patients who all begin treatment and are initially healthy.
Over two years, they may have a stroke, stop treatment (only at doctor visits), or die.
A routine doctor visit is scheduled about a year after treatment begins,
unless a stroke happens first, in which case a visit is likely to occur soon after.
Doctors are less likely to stop treatment after a stroke.
The chance of dying depends on whether the patient has had a stroke and whether they are still on treatment.

= Table with example coefficients

Consider the following example coefficients for the simulation mechanism, corresponding to a simulation mechanism,
which is compatible with the time-varying Cox model, e.g., $lambda_1^y = lambda_2^y = lambda_3^y$ (see e.g., @sec:intensities). We vary the treatment
effect on the outcome $beta_(k, A)^y$, corresponding to $beta_(k, A)^y > 0$, $beta_(k, A)^y = 0$, and $beta_(k, A)^y < 0$,
and the effect of a stroke on the outcome $beta_(k, L)^y$, corresponding to $beta_(k, L)^y > 0$, $beta_(k, L)^y = 0$, and $beta_(k, L)^y < 0$.
We also vary the effect of a stroke on the treatment propensity $alpha_(k, "L")$
and the effect of treatment on stroke $beta_(k, A)^ell$.

We consider three overall scenarios:
- *No baseline and time-varying confounding*.
- *No time-varying confounding but baseline confounding*.
- *Time-varying confounding*
- *Strong confounding*.

We highlight the interpretation of the most important parameters in the simulation mechanism:
- $alpha_(k, "age")$: If positive: You will more likely be treated if you are older.
- $alpha_(k, "L")$: If negative: You will be less likely to be treated if you have had a stroke.
- $beta_(k,"age")^x$: If positive: The risk of having a stroke or primary event increases with age.
- $beta_(k, A)^ell$: If negative: The risk of having a stroke is lower if you are treated.
- $beta_(k, L)^y$: If positive: The risk of having a primary event is higher if you have had a stroke.

Proposed values for the parameters are shown in the table below.
Each value is varied, holding the others fixed.
The values with bold font correspond to the values used
when fixed.
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

#pagebreak()

#align(center, [
#table(
  columns: ( auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
    [*Parameters*], [*Values*],
  ),
    [$alpha_(k 0)$], [0.3],
    [$alpha_(k, "age")$], [0.02],
    [$alpha_(k, "L")$], [*-0.1*, 0, 0.1],
    [$beta^y_(k, "age")$], [0.025],
    [$beta^ell_(k, "age")$], [0.015],
    [$beta^y_(k, A)$], [*-0.15*, 0, 0.15],
    [$beta^ell_(k, A)$], [*-0.2*, 0, 0.2],
    [$beta^y_(k, "L")$], [-0.25, 0, *0.25*],
    [$lambda_k^y$], [0.0001],
    [$lambda_k^ell$], [0.001],
    [$gamma_"age"$], [0],
    [$gamma_0$], [0.005]
)])

Strong confounding is considered in the following table
in two different simulation settings. 
#align(center, [
#table(
  columns: ( auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
    [*Parameters*], [*Values*],
  ),
    [$alpha_(k 0)$], [0.3],
    [$alpha_(k, "age")$], [0.02],
    [$alpha_(k, "L")$], [-0.3, 0.3],
    [$beta^y_(k, "age")$], [0.025],
    [$beta^ell_(k, "age")$], [0.015],
    [$beta^y_(k, A)$], [-0.4, 0.4],
    [$beta^ell_(k, A)$], [-0.2],
    [$beta^y_(k, "L")$], [0.5],
    [$lambda_k^y$], [0.0001],
    [$lambda_k^ell$], [0.001],
    [$gamma_"age"$], [0],
    [$gamma_0$], [0.005]
)])
Additionally, we consider the setting of no confounding
effect on treatment and outcome, i.e., we set
$alpha_(k, "L") = 0$ and $beta^y_(k, L) = 0$.
In this case, the corresponding table is:

#align(center, [
#table(
  columns: ( auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
    [*Parameters*], [*Values*],
  ),
    [$alpha_(k 0)$], [0.3],
    [$alpha_(k, "age")$], [0.02],
    [$alpha_(k, "L")$], [0],
    [$beta^y_(k, "age")$], [0.025],
    [$beta^ell_(k, "age")$], [0.015],
    [$beta^y_(k, A)$], [-0.15, 0, 0.15],
    [$beta^ell_(k, A)$], [-0.2],
    [$beta^y_(k, "L")$], [0],
    [$lambda_k^y$], [0.0001],
    [$lambda_k^ell$], [0.001],
    [$gamma_"age"$], [0],
    [$gamma_0$], [0.005]
)])

= Target estimand

We explain here what the target estimand is
and how to arrive at the iterative conditional expectation formula. 
Let $cumhazard( k, x, t)$ denote the cumulative cause-specific hazard function
for $event(k)$ and $status(k) = x$ at time $t$ given the history $history(k-1)$.
For instance, if $k=2$ and $x=y$, then in the simulation mechanism, we have
$
    cumhazard(2, y, t) = lambda^y_2 exp(beta^y_(2, "age") "age" + beta^y_(2, A) treat(1) + beta^y_(2, L) covariate(1)) 
$
Furthermore, let $densitytrt(t,k)$ denote the probability of being treated as the $k$'th event
given that you go to the doctor at time $t$, i.e., $status(k)=a$,
and your history $history(k-1)$.
If $k=2$, this equals in the simulation mechanism
$
    densitytrt(t, 2) = "expit"(alpha_(20) + alpha_(2, "age") "age" + alpha_(2, "L") covariate(1)) = "expit"(alpha_(20) + alpha_(2, "age") "age" + alpha_(2, "L") ).
$
Let, for convenience of notation, "age" be included in $L (0)$.
We "define"
$
    history(0) &= (treat(0), covariate(0)),\
    history(1) &= (event(1), status(1), treat(1), covariate(1), treat(0), covariate(0), "age"), \
    history(2) &= (event(2), status(2), treat(2), covariate(2), event(1), status(1), treat(1), covariate(1), treat(0), covariate(0), "age"),
$
Using the notation $f_(t_k) = (t_k, d_k, a_k, l_k, dots, a_0, l_0)$
with $f_0 = (a_0, l_0)$, we, analogously to @rytgaardContinuoustimeTargetedMinimum2022, define our target parameter $Psi_tau : cal(P) -> RR$
for a non-parametric model $cal(P)$ as
$
    Psi_tau (P) &= integral (integral_((0, tau]) (integral_((t_1,tau]) (integral_((t_2,tau])  product_(w_3 in (t_3, tau)) (1 - Lambda^y_3 (dif w_3 | f_(t_2))) Lambda_3^y (dif t_3 | f_(t_2))) \
        &qquad times  product_(w_2 in (t_2, tau)) (1 - sum_(x=a,y) Lambda^x_2 (dif w_2 | f_(t_1))) bb(1) {a_2=1} times Lambda_2^a (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        Lambda_1^ell (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) (integral_((t_1,tau]) (integral_((t_2,tau])  product_(w_3 in (t_3, tau)) (1 - Lambda^y_3 (dif w_3 | f_(t_2))) Lambda_3^y (dif t_3 | f_(t_2))) \
        &qquad times  product_(w_2 in (t_2, tau)) (1 - sum_(x=y,ell) Lambda^x_2 (dif w_2 | f_(t_1))) Lambda_2^ell (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        bb(1) {a_1 = 1} times Lambda_1^a (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) (integral_((t_1,tau])  product_(w_2 in (t_2, tau)) (1 - sum_(x=a,y) Lambda^x_2 (dif w_2 | f_(t_1)))  Lambda_2^y (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        Lambda_1^ell (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) (integral_((t_1,tau])  product_(w_2 in (t_2, tau)) (1 - sum_(x=a,y) Lambda^x_2 (dif w_2 | f_(t_1))) Lambda_2^y (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        bb(1) {a_1=1} times Lambda_1^a (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_(0))) Lambda_1^y (dif t_1 | f_(0))) P_(L(0)) (dif l_0),
$
corresponding to setting $densitytrt(t, k) = 1$.
This expression is fairly long and quite complicated.

We now explain how one goes from this apparently complicated expression
to the iterative conditional expectation formula,
which reduces the dimensionality of the problem significantly.

#example[
    First define,
    $
        , \
        Z^a_2 &= 
    $
    Writing,
    $
        &Z^a_3 = bb(1) {event(3) <= tau}, \ \
    &Qbar(2) (f_(t_2)) \
            &= mean(P) [Z^a_3 | history(2) = f_(t_2)]], \ \
            &Z^a_2 = bb(1) {event(2) <= tau, status(2) = y} + bb(1) {event(2) < tau, status(2) = ell} Qbar(2) (history(2)) + 
        bb(1) {event(2) < tau, status(2) = a} Qbar(2) (cal(F)^bold(1)_(event(2))) \
        
        &Qbar(1) (f_(t_1)) \
        &= mean(P) [Z_2^a | history(1) = f_(t_1)], \ \

            &Z^a_1 = bb(1) {event(1) <= tau, status(1) = y} + bb(1) {event(1) < tau, status(1) = ell} Qbar(1) (history(1)) +
        bb(1) {event(1) < tau, status(1) = a} Qbar(1) (cal(F)^bold(1)_(event(1))) \
        &Qbar(0) (f_0) \
        &= mean(P) [Z_1^a | history(0)=f_0],
$
and letting
$
    cal(F)^bold(1)_(event(2)) &= (event(2), status(2), 1, covariate(2), event(1), status(1), treat(1), covariate(1), treat(0), covariate(0), "age"),\
    cal(F)^bold(1)_(event(1)) &= (event(1), status(1), 1, covariate(1), treat(0), covariate(0), "age"),
$
Then, our claim is that $Psi_tau (P) = mean(P_(L(0))) [Qbar(0) (history(0))]$,
    where $P_(L(0))$ is the distribution of the baseline confounders.
]
#proof[

First note that,

$
    P (event(k) <= t, status(k) = x | history(k-1) = f_(t_(k-1))) = integral_((t_(k-1), s]) product_(u in (t_(k-1), s)) (1 - sum_(x=a,ell,y) Lambda^x_k (dif u | f_(t_(k-1)))) Lambda^x_k (dif s | f_(t_(k-1))) , t < tauend
$
for $x = y, ell$ by definition
and
$
    &P (event(k) <= t, status(k) = a, treat(k) = 1 | history(k-1) = f_(t_(k-1))) \
        &qquad = integral_((t_(k-1), s]) product_(u in (t_(k-1), s)) (1 - sum_(x=a,ell,y) Lambda^x_k (dif u | f_(t_(k-1)))) pi_k (event(k), history(k-1)) Lambda^a_k (dif s | f_(t_(k-1))) 
$
and
$
    &P (event(k) <= t, status(k) = a, treat(k) = 0 | history(k-1) = f_(t_(k-1))) \
        &qquad = integral_((t_(k-1), s]) product_(u in (t_(k-1), s)) (1 - sum_(x=a,ell,y) Lambda^x_k (dif u | f_(t_(k-1)))) (1 - pi_k (event(k), history(k-1))) Lambda^a_k (dif s | f_(t_(k-1)))
$

Now, we can rewrite the target parameter as follows:
$
    Psi_tau (P) &= mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = ell}  mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1)))  \
        &qquad qquad times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))  mean(P) [ bb(1) {event(2) < tau, status(2) = ell}  \
            &qquad qquad times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = ell} mean(P) [bb(1) {event(2) <= tau, status(2) = y} | history(1)] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = a}) /(pi_1 (event(1), history(0))) bb(1) {treat(1) = 1} mean(P) [bb(1) {event(2) <= tau, status(2) = y} | history(1)] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [bb(1) {event(1) <= tau, status(1) = y}  | history(0)] ] \
        &= mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
            &qquad times mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1)))  \
                &qquad qquad times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
            &qquad times mean(P) [ bb(1) {event(2) < tau, status(2) = ell} times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + (bb(1) {event(1) < tau, status(1) = a}) /(pi_1 (event(1), history(0))) bb(1) {treat(1) = 1}) \
            &qquad times mean(P) [bb(1) {event(2) <= tau, status(2) = y} | history(1)] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [bb(1) {event(1) <= tau, status(1) = y}  | history(0)] ] 
$ <eq:something>
where we simply add terms which are zero corresponding to two treatments and two strokes
and we let $P_(L(0))$ denote the distribution of the baseline confounders.

(i.e., the history where we set the _current_ treatment to 1),
we will argue that $Psi_tau (P) = mean(P_(L(0))) [Qbar(0) (history(0))]$.
Using, @eq:something, we can rewrite the target parameter as follows:
$
    Psi_tau (P) &=^(*) mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
        &qquad times mean(P) [bb(1) {event(2) < tau, status(2) = a} Qbar(2) (cal(F)^bold(1)_(event(2)))| history(1) ] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
            &qquad times mean(P) [ bb(1) {event(2) < tau, status(2) = ell} Qbar(2) (history(2)) | history(1) ] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + (bb(1) {event(1) < tau, status(1) = a}) /(pi_1 (event(1), history(0))) bb(1) {treat(1) = 1}) \
            &qquad times mean(P) [bb(1) {event(2) <= tau, status(2) = y} | history(1)] | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [bb(1) {event(1) <= tau, status(1) = y}  | history(0)] ] \
        &= mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
            &qquad times Qbar(1) (history(1))  | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [bb(1) {event(1) <= tau, status(1) = y}  | history(0)] ] \
        &=^(**) mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = ell} Qbar(1) (history(1)) + bb(1) {event(1) < tau, status(1) = a} Qbar(1) (cal(F)^1_(event(1)))
            &+ bb(1) {event(1) <= tau, status(1) = y} | history(0)] ] \
        &+ mean(P_(L(0))) [mean(P) [bb(1) {event(1) <= tau, status(1) = y}  | history(0)] ] \
        &= mean(P_(L(0))) [Qbar(0) (history(0))].
$
In $*$, we used that
$
    &mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1))) Qbar(2) (history(2)) | history(1) ]\
        &=mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1))) Qbar(2) (cal(F)^bold(1)_(event(2))) | history(1) ]\
        &=mean(P) [ bb(1) {event(2) < tau, status(2) = a} (mean(P) [bb(1) {treat(2)=1} | history(1), status(2), event(2) ])/(pi_2 (event(2), history(1))) Qbar(2) (cal(F)^bold(1)_(event(2))) | history(1) ]\
        &=mean(P) [ bb(1) {event(2) < tau, status(2) = a} Qbar(2) (cal(F)^bold(1)_(event(2))) | history(1) ],
$
by the law of iterated expectation. Similarly, in $**$, we used that
$
    &mean(P) [bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = a} )/(pi_1 (event(1), history(0))) Qbar(1) (history(1)) | history(0)] \
        &=mean(P) [bb(1) {event(1) < tau, status(1) = a} Qbar(1) (cal(F)^bold(1)_(event(1))) | history(0)],
$
]
Thus, regression techniques can be used to estimate the target parameter $Psi_tau (P)$.
Not only can it be used for the estimates of the target parameter,
but it turns that the terms $
    Qbar(0)$, $Qbar(1)$, and $Qbar(2)$, $Psi_tau (P)$,
as well as $pi_k (t, history(k-1))$ are precisely the terms
we encounter in the efficient influence function. Therefore, inference
can be obtained as part of the procedure
where we estimate $Qbar(0)$, $Qbar(1)$, and $Qbar(2)$ by considering a one-step estimator.
Furthermore, the resulting estimator will be doubly robust. 

== Example usage of the Algorithm <section:example>

To help illustrate the algorithm, we present a simple example in @fig:longitudinaldataice in the case where $tau = 5$.
We start at $k=3$.
As in the rest of the paper, we suppose that the time horizon is $tau = 720$.

#outline-colorbox(
      title: [Iteration $k=3$],
        color: "blue",
        radius: 2pt,
    width: auto,
    centering: true,
)[
    Denote by $R_(3,tau) $ the set of people for which it is possible that may die as their
    third event before time $tau$, that is people with $event(2) < tau$ and $event(2) in {a, ell}$
    (otherwise the probability we are trying to determine is zero).
    We find that $R_(3,tau) = {6, 7}$.
    For each of these people find $Z^a_(3)$ and regress on $historycensored(2)$ to obtain a prediction function $hat(nu)_(2)$.
    In *R*, this can be done as follows via e.g., `glm` assuming the data is given as `data`:
    ```r        
    D_3 <- data[data$status_2 %in% c("a", "l") & data$time_2 < tau, ] ## data set  thatconsists of ids from R_3
    data$Z_3 <- 1*(D_3$time_3 <= tau)
    fit <- glm(Z_3 ~ time_2+status_2+A_2+L_2+ time_1+status_1+A_1+L_1+A_0+L_0+age, data = D_3, family = "binomial")
    hat_nu_2 <- function(data) { predict(fit, newdata=data, type = "response")}
    ```
          ]
#outline-colorbox(
        title: [Iteration $k=2$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

As in the case $k=3$, we find $R_(2,tau) = {3, 4, 6, 7}$.
- For $i=3$, we produce the altered history, where
                $cal(F)^1_(macron(T)_(2,i)) = (55,0, 1,1, 1,62, ell, 1, 1)$ to $hat(nu)_2$
                and find $hat(nu)_2 (cal(F)^1_(macron(T)_(2,i)))$.
                Based on this we calculate $hat(Z)^a_(2,i) = 1 times hat(nu)_2 (cal(F)^1_(macron(T)_(2,i)))$.
- For $i = 4$, we apply the actual history $cal(F)_(macron(T)_(2,4))$ to $hat(nu)_2$. Again,
  we calculate $hat(Z)^a_(2,4) = 1 times cal(F)_(macron(T)_(2,4))$.
- For $i=7$, similarly calculate $hat(Z)^a_(2,4) = 1 cal(F)_(macron(T)_(2,6))$.
- For $i=6$, we simply find $hat(Z)^a_(2,7) = 1$.
Regress the predicted values $hat(Z)^a_(2)$ on $historycensored(1)$ to obtain a prediction function $hat(nu)_(1)$.
                In *R*, this can be done as follows via e.g., `lm` assuming the data is given as `data`:
                ```r
                D_2 <- data[data$status_1 %in% c("a", "l") & data$time_1 < tau, ] ## data set that consists of ids from R_2
                D_2^a <- copy(data)
                D_2^a[data$status_2 == "a", "treat_2"] <- 1 ## alter treat_2 to 1 for those with status_2 = a
                data$Z_2 <- 1*(D_2$time_2 <= tau & D_2$status_2 == "y") + 
                    1*(D_2$time_2 < tau & D_2$status_2 == "l") * hat_nu_2(D_2) + 
                    1*(D_2$time_2 < tau & D_2$status_2 == "a") * hat_nu_2(D_2)
                fit <- lm(Z_2 ~ time_1+status_1+A_1+L_1+A_0+L_0+age, data = D_2)
                hat_nu_1 <- function(data) { predict(fit, newdata=data, type = "response")}
                ```
            ]
#outline-colorbox(
        title: [Iteration $k=1$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

Same procedure as $k=2$. Note that we find $R_(1,tau) = {1, 2, 3, 4, 5, 6, 7}$.
            ]
#outline-colorbox(
        title: [Iteration $k=0$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

We get the estimate $hat(Psi)_n = 1/7 sum_(i=1)^7 hat(nu)_(0) (1, 0, "sex"_i (0))$ for $n=7$,
where we obtained $hat(nu)_(0)$ from $k=1$.
            ]

#figure(table(
    columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto),
                inset: 10pt,
    table.header(
        [id], [age],[$covariate(0)$], [$treat(0)$], 
        [$covariate(1)$], [$treat(1)$], [$event(1)$], [$status(1)$],
        [$covariate(2)$], [$treat(2)$], [$event(2)$], [$status(2)$],
        [$event(3)$], [$status(3)$]
    ),
    [1], [60], [0], [1], [0], [1], [745], [$a$], [Ø], [Ø], [770], [$y$], [$oo$], [Ø],
    [2], [50],[0], [1], [Ø], [Ø], [140], [$y$], [Ø], [Ø], [$oo$], [Ø], [$oo$], [Ø],
    [3], [55],[0], [1], [1], [1], [62], [$ell$], [1], [0], [850], [$a$], [$870$], [$y$],
    [4], [46],[0], [1], [1], [1], [70], [$ell$], [1], [1], [170], [$a$], [$182$], [$y$],
    [5], [67],[0], [1], [Ø], [Ø], [60], [$y$], [Ø], [Ø], [$oo$], [Ø], [$oo$], [Ø],
    [6], [52],[0], [1], [1], [1], [120], [$ell$], [Ø], [Ø], [175], [$y$], [$oo$], [Ø],
    [7], [56], [0], [1], [0], [0], [40], [$a$], [1], [0], [80], [$ell$], [$645$], [$y$],

                ),
                caption: [
                    Example data for illustration of the ICE algorithm. 
                ])<fig:longitudinaldataice>

= Modeling

To apply our debiased ICE estimator in the uncensored situation, we need to estimate
two types of nuisance parameters:
1. The treatment propensity $pi_k (t, history(k-1))$ for each $k = 1, dots, K$.
2. The conditional counterfactual probabilities $Qbar(k)$ for each $k = 1, dots, K$.

For $k = 3$, recall that
$
    history(2) = ("age", treat(1), covariate(1), event(1), status(1), treat(2), covariate(2), event(2), status(2)).
$

We need to estimate 
$
    Qbar(2) = P( event(3) <= tau, status(3) = y | history(2))
$
Note that it is 0 if $event(2) < tau$ or $status(2) = y$,
as in that case $event(3) > tau$,
so we only need to estimate it for the individuals who are still at risk, i.e., those with $event(2) < tau$ and $status(2) != y$.
This can be estimated by e.g., logistic regression.
Importantly, in this first step, we do not impose any intervention,
as you cannot visit the doctor for $k=3$.
Denote this estimator by $hat(nu)_2$ of $Qbar(2)$.

For $k=2$, we should model
the conditional counterfactual probability $Qbar(1)$ of
having the primary event within $tau = 720$ days
given the history $history(1)$, among the people who are still at risk $(event(1) < tau and status(1) != y)$
using the model for $k=3$, see e.g., the main note for elaboration
on why $Qbar(1)$ has this interpretation.
Here
$
    history(1) = ("age", treat(1), covariate(1), event(1), status(1)).
$

As described in the section "Algorithm for ICE-IPCW Estimator" (set $hat(S)^c = 1$ in the algorithm),
this is done by calculating $hat(Z)^a_1$ (outcome) for each individual at risk using $hat(nu)_2$,
and regressing on $history(1)$ (covariates).
We apply a generalized linear model (GLM) with the option `family = quasibinomial`.
The resulting estimator is denoted $hat(nu)_1$ which can provide
predictions for the conditional counterfactual probability of having a primary event within $tau = 720$ days
given the information that you have after one event. 

For $k=1$, we need to estimate the conditional probability of
having a stroke within $tau = 720$ days given the history $history(0)$ for all individuals.

For the treatment propensity, we can simply estimate this using
logistic regression. For instance
$pi_(k) (t, history(k-1))$ can be estimated
by regressing $treat(k)$ on
$history(k-1)$ and $event(k)$ among people with $status(k-1) = a, ell$ and $status(k) = a$.

= Extensions
Let $T^ell$ be the time since the last stroke (i.e., 0 if stroke occurred as the previous event and $event(2)-event(1)$ if it happened as the first event).
Then, we might consider
$
    S_((3))^y tilde "Exp"(lambda^y_3 exp(beta^y_(3,"age") "age" + beta^y_(3, A) treat(2) + beta^y_(3, L) covariate(2) + beta^y_(3, T^ell) T^ell)),
$
or we might consider a model in which the baseline hazard is not constant.
It also might be easier to state a realistic model in terms of the intensities directly,
in which case, we can then "transform" to the interevent scale. For example, a realistic intensity for the primary event,
$
    lambda^y (t) &= lambda_0^y (t) exp(beta^y_("age") "age") exp(beta_L^y exp(beta^(y *)_L (t-T^ell)) L(t-) + beta_A^y  exp(beta^(y *)_A (t-T^a)) (1-A(t-)) \
        &+ beta^y_Z bb(1) {event(2) < t} bb(1) {status(1)=a} bb(1) {status(2)=ell}) bb(1) {t <= T^y}
$
Here $T^a$ denotes the time to the last treatment. 
Note that each term is zero if the corresponding event has not happened yet, so we do not condition on the future. 
Here, we can let each coefficient depend on event number, but for simplicity of notation, we do not do so.
The last term corresponds to there being an effect of the order in which the events happened
after two events. 
This is one way to include longe range dependencies.
Simulating from this model is significantly more complicated, because we have to rely on numeric integration.

More generally, let $cumhazard(k, x, t)$ denote the cumulative hazard function for the $k$'th event of type $x$ at time $t$
conditional on the history $history(k-1)$.
The cumulative hazard-cause specific hazard of $S_((k))$ of the $k$'th event type $x$ is given by
$
    [tauend - event(k-1), 0) in.rev t mapsto cumhazard(k, x, t + event(k-1)) - Lambda^x_k (event(k-1), history(k-2))
$
If we suppose for simplicity that $cumhazard(k, x, t)$ is invertible on $(event(k-1), tauend]$
with say inverse $Lambda^(-1,x)_k (dot,history(k-1))$
letting $E tilde "Exp"(1)$ be an exponential random variable with mean 1,
we can simulate $S_((k))^x$ as follows
$
    S_((k))^x = Lambda^(-1,x)_k (E + Lambda^x_k (event(k-1), history(k-2)),history(k-2))  - event(k-1),
$
This can be seen by using the fact that if $Lambda$ is a cumulative hazard function for the random variable $T$,
then $Lambda^(-1) (E)$ is a random variable with the same distribution as $T$.

= Intensities <sec:intensities>

It is illustrative to compare the simulation mechanism with a
model for the intensities. Furthermore, we argue that
observations from a counterfactual distribution can be simulated
by setting $treat(k) = 1$ for each $k = 1, dots, K$.

First, let us define the counting processes as
$
    N^y (t) &= sum_(k=1)^3 bb(1) {status(k) = y, event(k) <= t}, \
    N^ell (t) &= sum_(k=1)^2 bb(1) {status(k) = ell, event(k) <= t}, \
    N^(a 1) (t) &= sum_(k=1)^2 bb(1) {status(k) = a, event(k) <= t, treat(k) = 1}, \
        N^(a 0) (t) &= sum_(k=1)^2 bb(1) {status(k) = a, event(k) <= t, treat(k) = 0}.
$
Using Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose"),
we find that $N^y$ has the compensator
$
    Lambda^y (t) &= integral_0^t sum_(k=1)^3 bb(1) {event(k-1) < s <= event(k)} lambda_k^y exp(beta^y_(k, "age") "age" + beta^y_(k, A) treat(k-1) + beta^y_(k, L) covariate(k-1)) dif s 
$
If $lambda_1^y = lambda_2^y = lambda_3^y$, we can write the intensity as
$
    lambda^y (t) &= lambda_1^y \
        &exp(beta^y_(k, "age") "age") exp( beta^y_(1, A) A(t-) + (beta^y_(2, A)-beta^y_(1, A)) bb(1) {event(1) < t <= event(2)}  A(t-) \
            &qquad + (beta^y_(3, A)-beta^y_(2, A)) bb(1) {event(2) < t <= event(3)}  A(t-) + beta^y_(1, "L") L(t-) \
            &qquad + (beta^y_(2, "L")-beta^y_(1, "L")) bb(1) {event(1) < t <= event(2)} L(t-) \
            &qquad + (beta^y_(3, "L")-beta^y_(2, "L")) bb(1) {event(2) < t <= event(3)} L(t-)) bb(1) {t <= event(3) and tauend} \
$
which shows that the model is compatible with the time-varying Cox model.
We may find a similar expression for $N^ell$.

Let $pi_t (a) = sum_(k=1)^2 bb(1) {event(k-1) < t <= event(k)} "expit" (alpha_(k 0) + alpha_(k, "age") "age" + alpha_(k, "L") covariate(k-1))$
and $pi_t^* (a) = sum_(k=1)^2 bb(1) {event(k-1) < t <= event(k)} bb(1) {a= 1}$.
Let $lambda^a$ be defined analogously to $lambda^y$, then we find
via Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose"),
that $N^(a 1)$ and $N^(a 0)$ have the compensators
$
        Lambda^(a 1) (t) &= integral_0^t pi_s (1) lambda^a (s) dif s, \
        Lambda^(a 0) (t) &= integral_0^t pi_s (0) lambda^a (s) dif s.
$
respectively. Simulating from the interventional mechanism corresponds to
having the compensators
$
    Lambda^(a 1) (t) &= integral_0^t pi_s^* (1) lambda^a (s) dif s, \
        Lambda^(a 0) (t) &= integral_0^t pi_s^* (0) lambda^a (s) dif s.
$
with the other compensators unchanged, which is the continuous time $g$-formula. 

#bibliography("ref.bib", style: "apa")


