#import "definitions.typ": *

= Simulating longitudinal data for time-to-event analysis in continuous time.
Each observation $O= (event(K), status(K), treat(K-1), covariate(K-1), event(K-1), status(K-1), dots, treat(0), covariate(0))$
is generated in the following way. Recall from the main note
that we put $history(k) = sigma(event(k), status(k), treat(k-1), covariate(k-1)) or history(k-1)$.

Let $densitytrt(t, k)$ be the probability of being treated at the $k$'th event given $status(k) =a, event(k) = t$, and $history(k-1)$.
Similarly, let $densitycov(t, dot, k)$ be the probability measure for the covariate value given $status(k) = ell, event(k) = t$, and $history(k-1)$.
Let also $cumhazard(k, x, dif t)$ be the cumulative cause-specific hazard measure
for the $k$'th event and cause $x$ given $history(k-1)$, where $x = a, ell, d, y, c$.
At baseline, we let $pi_0 (covariate(0))$ be the probability of being treated given $covariate(0)$
and $mu_0 (dot)$ be the probability measure for the covariate value.

We let $L(t)$ consist of the covariates _age_, _sex_, $L_1 (t)$, $L_2 (t)$ (e.g., recurrent events).
Then we generate the baseline variables as follows
$
    &"age" tilde "Unif"(40,90) \
        &"sex" tilde "Bernoulli"(0.4) \
        &L_1 (0) tilde "Bernoulli"(0.4) \
        &L_2 (0) tilde "Bernoulli"(0.25) \
        & treat(0)  tilde "Bernoulli"("expit"((beta_0^a)^T cal(F)_(0)^"-A"+beta^(a,*)_0)),
$
where $cal(F)_(0)^"-A" = ("age", "sex", L_1 (0), L_2 (0))$.

Then, the observation is drawn iteratively as follows,

$
    &S_((k))^x | history(k-1) = f_(t_(k-1)) tilde "Exp"(lambda^x_k exp((beta^x_k)^T f_(t_(k-1)))), x = a, ell, d, y, c \
        &status(k) = x "if" S_((k))^x < S_((k))^z "for all" z != x \
        &event(k) = event(k-1) + S_((k))^x "if" status(k) = x \
        &L^* | event(k), history(k-1) = f_(t_(k-1))tilde "Bernoulli(expit("alpha^L_k)^T f_(t_(k-1)) + alpha^(L,*)_k) \
        &L_1 (0) = cases(L_1 (k-1) + L^* "if" status(k) = ell "and" k < K, L_1 (k-1) "otherwise") \
        &L_2 (0) = cases(L_2 (k-1) + L^* "if" status(k) = ell "and" k < K, L_2 (k-1) "otherwise") \
        &treat(k) = "Bernoulli(expit("(alpha^A k)^T f_(t_(k-1)) + alpha^(A,*)_k)) "if" status(k) = a \
$

where Exp$(lambda)$ denotes the exponential distribution with rate $lambda$.
When the static intervention is applied, we put $treat(k) = 1$ for each $k = 1, dots, K$.
When the uncensored data argument is used, we put $S_((k))^c = oo$.
So the parameters we can vary are the $alpha$'s, $beta$'s, and $lambda$'s.
A limitation of the current implementation is that the Markov assumption is used for the time-varying variables, i.e.,
$S_((k))^x$ depends only on $history(k-1)$ through $(treat(k-1), covariate(k-1), event(k-1), status(k-1))$.
