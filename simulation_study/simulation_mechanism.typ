#import "definitions.typ": *

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
If the first event was a terminal event -- either outcome or administrative censoring --
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
Some explanation for this is warranted. 
//It is not too difficult to see that the likelihood factorizes as in #cite(<rytgaardContinuoustimeTargetedMinimum2022>, form: "prose")
//corresponding to the intervention that we are interested in (see e.g., Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose")).

= Intensities

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

== Modeling

In the uncensored situation, we need two models for each event point $k = 1, 2, 3$ (except the last).
We also do not need a model for the baseline treatment. 

For $k = 3$, recall that
$
    history(2) = ("age", treat(1), covariate(1), event(1), status(1), treat(2), covariate(2), event(2), status(2)).
$

We need to estimate 
$
    Qbar(2) = P( event(3) <= tau, status(3) = y | history(2))
$
Note that it is 0 if $event(2) < tau$ or $status(2) = y$,
as in that case $event(3) > tau$.
This can be estimated by e.g., logistic regression.
Importantly, in this first step, we do not impose any intervention,
as you cannot visit the doctor for $k=3$.

For $k=2$, the model should model
the conditional counterfactual probability of
having the primary event within $tau = 720$ days
given the history $history(1)$, among the people who are still at risk $(event(1) < tau and status(1) != y)$.

For $k=1$, we need to estimate the conditional probability of
having a stroke within $tau = 720$ days given the history $history(0)$ for all individuals.

For the treatment propensity, we can simply estimate this using
logistic regression. For instance
$pi_(k) (t, history(k-1))$ can be estimated
by regressing $treat(k)$ on
$history(k-1)$ and $event(k)$ among people with $status(k-1) = a, ell$ and $status(k) = a$.

== Table with example coefficients

Consider the following example coefficients for the simulation mechanism, corresponding to a simulation mechanism,
which is compatible with the time-varying Cox model, e.g., $lambda_1^y = lambda_2^y = lambda_3^y$. We vary the treatment
effect on the outcome $beta_(k, A)^y$, corresponding to $beta_(k, A)^y > 0$, $beta_(k, A)^y = 0$, and $beta_(k, A)^y < 0$,
and the effect of a stroke on the outcome $beta_(k, L)^y$, corresponding to $beta_(k, L)^y > 0$, $beta_(k, L)^y = 0$, and $beta_(k, L)^y < 0$.
We also vary the effect of a stroke on the treatment propensity $alpha_(k, "L")$.

We highlight the interpretation of the most important parameters in the simulation mechanism:
- $alpha_(k, "age")$: If positive: You will more likely be treated if you are older.
- $alpha_(k, "L")$: If negative: You will be less likely to be treated if you have had a stroke.
- $beta_(k,"age")^x$: If positive: The risk of having a stroke or primary event increases with age.
- $beta_(k, A)^ell$: If negative: The risk of having a stroke is lower if you are treated.
- $beta_(k, L)^y$: If positive: The risk of having a primary event is higher if you have had a stroke.

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
    [$alpha_(k, "L")$], [-0.1, 0, 0.1],
    [$beta^y_(k, "age")$], [0.025],
    [$beta^ell_(k, "age")$], [0.015],
    [$beta^y_(k, A)$], [-0.15, 0, 0.15],
    [$beta^ell_(k, A)$], [-0.2],
    [$beta^y_(k, "L")$], [-0.25, 0, 0.25],
    [$lambda_k^y$], [0.0001],
    [$lambda_k^ell$], [0.001],
    [$gamma_"age"$], [0],
    [$gamma_0$], [0.005]
)])

= Extensions
Let $T^ell$ be the time since the last stroke (i.e., 0 if stroke occurred as the previous event and $event(2)-event(1)$ if it happened as the first event).
Then, we might consider
$
    S_((3))^y tilde "Exp"(lambda^y_3 exp(beta^y_(3,"age") "age" + beta^y_(3, A) treat(2) + beta^y_(3, L) covariate(2) + beta^y_(3, T^ell) T^ell)),
$
or we might consider a model in which the baseline hazard is not constant.

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

= Plain Language Summary (for Clinical Audience)

We simulate patients who all begin treatment and are initially healthy.
Over two years, they may have a stroke, stop treatment (only at doctor visits), or die.
A routine doctor visit is scheduled about a year after treatment begins,
unless a stroke happens first, in which case a visit is likely to occur soon after.
Doctors are less likely to stop treatment after a stroke.
The chance of dying depends on whether the patient has had a stroke and whether they are still on treatment.

#bibliography("ref.bib", style: "apa")
