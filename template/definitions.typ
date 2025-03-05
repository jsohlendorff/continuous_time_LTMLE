#import "@preview/fletcher:0.5.5": node, edge, diagram
#import "@preview/ctheorems:1.1.3": *

#let citep = cite.with(form: "normal")

// event definitions
#let event(ind) = {
  if ind == [0] or ind == 0 [
    $T_0$
  ] else {
    $T_((#ind))$
  }
}


#let eventcens(ind) = {
  if ind == [0] or ind == 0 [
      $tilde(T)_0$
  ] else {
      $tilde(T)_((#ind))$
  }
}

#let eventint(ind) = {
  if type(ind) == "integer" {
    let indminus = ind - 1
    if (indminus != 0){
      $T_((#ind))^(macron(a)_(#indminus))$
    } else {
      $T_((#ind))^(a_0)$
    }
  } else if ind.has("children") and ind.children.len() == 3 and ind.children.at(1) == [+] and regex("\d+") in ind.children.at(2).text{
    let theInteger = int(ind.children.at(2).text)-1
    if (theInteger != 0){
        $T_((#ind))^(macron(a)_(#ind.children.at(0) + #theInteger))$
    } else {
      $T_((#ind))^(macron(a)_(#ind.children.at(0)))$
    }
  } else {
      $T_((#ind))^(macron(a)_(#ind - 1))$
  }
}

#let statusint(ind) = {
    if type(ind) == "integer" {
        let indminus = ind - 1
        if ind == [0] or ind == 0 {
            $D_0$
        } else {
            $D_((#ind))^(a_(#indminus))$
        }
    } else if ind.has("children") and ind.children.len() == 3 and ind.children.at(1) == [+] and regex("\d+") in ind.children.at(2).text{
        let theInteger = int(ind.children.at(2).text)-1
        if theInteger == 0 {
            $D_((#ind))^(a_0)$
        } else {
            $D_((#ind))^(macron(a)_(#theInteger))$
        }
    } else {
        $D_((#ind))^(macron(a)_(#ind - 1))$
    }
}

#let history(eventno) = {
  if eventno == [0] or eventno == 0 [
    $cal(F)_0$
  ] else [
    $cal(F)_(event(#eventno))$
  ]
}

#let historypast(eventno) = $underline(history(#eventno))$
#let historynext(eventno) = $overline(history(#eventno))$

#let historyint(eventno) = {
  if eventno == [0] or eventno == 0 [
      $cal(F)_0^(a_0)$
  ] else [
      $cal(F)^a_(event(#eventno))$
  ]
}

#let hazard(which, var, eventno) = {
    $lambda_(#eventno)^(#which)(#var, history(#eventno))$
}

#let cumhazard(eventno, which, var) = {
    $Lambda_(#eventno)^(#which)(#var, history(#eventno))$
}

#let treat(which) = {
    if which == [0] or which == 0 [
        $A_0$
    ] else {
        $A(event(#which))$
    }
}

#let status(which) = {
    $D_((#which))$
}

#let statuscens(which) = {

    $tilde(D)_((#which))$
}

#let covariate(which) = {
    if which == [0] or which == 0 [
        $L_0$
    ] else {
        $L(event(#which))$
    }
}

#let covariateint(which) = {
    if type(which) == "integer" {
        let indminus = which - 1
        if which == [0] or which == 0 {
            $L^(a_0)(0)$
        } else {
            $L^(macron(a)_(#indminus)) (eventint(#which))$
        }
    } else if which.has("children") and which.children.len() == 3 and which.children.at(1) == [+] and regex("\d+") in which.children.at(2).text{
        let theInteger = int(which.children.at(2).text)-1
        if theInteger == 0 {
            $L^(macron(a)_(#which.children.at(0))(eventint(#which))$
        } else {
            $L^(macron(a)_((#which.children.at(0) + #theInteger)))(eventint(#which))$
        }
    } else {
        $L^(macron(a)_(#which - 1))(eventint(#which))$
    }
}

#let densitytrt(time, arg, which) = $pi_(#which) (#time, #arg, history(#which))$
#let densitytrtint(time, arg, which) = $pi_(#which)^* (#time, #arg, history(#which))$
#let densitycov(time, arg, which) = $mu_(#which) (#time, #arg, history(#which))$

#let commonintegral(k, t, integrand, u) = {
    $integral_(event(#k))^(#t) #integrand upright(d) #u$
}

#let survivalfunction(k, s, sumset) = {
    $exp lr((- sum_(x in sumset) commonintegral(#k, #s, hazard(x, u, #k), u)))$
}

#let tauend = $tau_("end")$

#let edgemsm = edge.with(marks: "->", label-angle: auto)

#let edgemsmcens = edge.with(marks: "-->", label-angle: auto)

#let dagnode = node.with(width: 1.1cm, height: 1.1cm)

#let Qbar(k) = $macron(Q)_(#k, tau)^a$
#let Qbarmiss(k) = $macron(Q)_(#k)$
#let Qtilde(k) = $tilde(Q)_#k^a$
#let Qtildemiss(k) = $tilde(Q)_#k$
#let mean(k) = $bb(E)_#k$

#show: thmrules.with(qed-symbol: $square$)
#let unary(first, ..) = first
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"), base_level: 0)
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee"), base_level: 0)
#let assumption = thmbox("assumption", "Assumption", fill: rgb("#eeeeff"), base_level: 0)
#let definition = thmbox("definition", "Definition", fill: rgb("#ffeeee"), base_level: 0)
#let proof = thmproof("proof", "Proof")
#let atrisk(k, t) = $tilde(Y)_#k (#t)$

#let frange(x, y, step) = {
    assert(step != 0, message: "step must not be zero")
    assert(x < y, message: "y must be greater than x")
    let res = ()
    let inc = x
    while inc < y {
      res.push(inc)
      inc += step
    }
    res
  }

