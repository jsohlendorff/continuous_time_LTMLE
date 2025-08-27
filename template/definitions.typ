#import "@preview/fletcher:0.5.7": node, edge, diagram
#import "@preview/ctheorems:1.1.3": *
#import "@preview/cetz:0.3.4"
#import "@preview/algo:0.3.6": algo, i, d, comment, code

#let qquad = h(1.5cm)
//#show: checklist
#let citep(label) = cite(label, form: "normal")
#let evaluated(expr, size: 100%) = $lr(#expr|, size: #size)$
#let comment = comment.with(inline:true)

// event definitions
#let event(ind) = {
  if ind == [0] or ind == 0 [
    $T_0$
  ] else {
    $T_((#ind))$
  }
}

#let eventcensored(ind) = {
  if ind == [0] or ind == 0 [
      $macron(T)_0$
  ] else {
      $macron(T)_((#ind))$
  }
}

#let eventcensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $macron(T)_(0,i)$
  ] else {
      $macron(T)_((#ind),i)$
  }
}

#let statuscensored(ind) = {
  if ind == [0] or ind == 0 [
      $macron(Delta)_0$
  ] else {
      $macron(Delta)_((#ind))$
  }
}

#let statuscensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $macron(Delta)_(0,i)$
  ] else {
      $macron(Delta)_((#ind),i)$
  }
}

#let treatcensored(ind) = {
  if ind == [0] or ind == 0 [
      $A_0$
  ] else {
      $macron(A) (macron(T)_((#ind)))$
  }
}

#let treatcensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $macron(A)_(0,i)$
  ] else {
      $macron(A)_((#ind),i)$
  }
}

#let covariatecensored(ind) = {
  if ind == [0] or ind == 0 [
      $L_0$
  ] else {
      $L (macron(T)_((#ind)))$
  }
}

#let covariatecensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $L_(0,i)$
  ] else {
      $L_((#ind),i)$
  }
}

#let historycensored(ind) = {
  if ind == [0] or ind == 0 [
    $cal(F)_0$
  ] else [
      $cal(F)^tilde(beta)_(eventcensored(#ind))$
  ]
}

#let historycensoredi(ind) = {
  if ind == [0] or ind == 0 [
    $cal(F)_(0,i)$
  ] else [
      $cal(F)^tilde(beta)_((#ind),i)$
  ]
}

#let history(eventno) = {
  if eventno == [0] or eventno == 0 [
    $cal(F)_0$
  ] else [
    $cal(F)_(event(#eventno))$
  ]
}

#let cumhazardcensored(eventno, which, var) = {
    $tilde(Lambda)_(#eventno)^(#which)(#var, cal(F)^beta_(macron(T)_((#eventno - 1))))$
}
#let cumhazardcensoredprev(eventno, which, var) = {
    $tilde(Lambda)_(#eventno+1)^(#which)(#var, cal(F)^beta_(macron(T)_((#eventno))))$
}

#let historypast(eventno) = $underline(history(#eventno))$
#let historynext(eventno) = $overline(history(#eventno))$

#let hazard(which, var, eventno) = {
    $Lambda_(#eventno)^(#which)(#var, cal(F)_(T_((#eventno - 1))))$
}

#let cumhazard(eventno, which, var) = {
    $Lambda_(#eventno)^(#which)(#var, cal(F)_(T_((#eventno - 1))))$
}
#let cumhazardprev(eventno, which, var) = {
    $Lambda_(#eventno + 1)^(#which)(#var, cal(F)_(T_((#eventno))))$
}

#let treat(which) = {
    if which == [0] or which == 0 [
        $A(0)$
    ] else {
        $A(event(#which))$
    }
}

#let status(which) = {
    $Delta_((#which))$
}

#let statuscensored(which) = {
    $macron(Delta)_((#which))$
}

#let covariate(which) = {
    if which == [0] or which == 0 [
        $L(0)$
    ] else {
        $L(event(#which))$
    }
}

#let covariatecensored(which) = {
    if which == [0] or which == 0 [
        $L(0)$
    ] else {
        $L (macron(T)_(#which))$
    }
}

#let treatcensored(which) = {
    if which == [0] or which == 0 [
        $macron(A)_0$
    ] else {
        $A (macron(T)_(#which))$
    }
}

#let densitytrt(time, which) = $pi_(#which) (#time, covariate(#which), history(#which - 1))$
#let densitytrtcensored(time, which) = $pi_(#which) (#time, covariatecensored(#which), historycensored(#which - 1))$
#let densitycova(time, arg, which) = $mu^a_(#which) (#time, #arg, history(#which - 1))$
#let densitycovl(time, arg, which) = $mu^ell_(#which) (#time, #arg, history(#which - 1))$
#let densitycovcensored(time, arg, which) = $mu_(#which) (#time, #arg, historycensored(#which - 1))$

#let tauend = $tau_("end")$

#let edgemsm = edge.with(marks: "->", label-angle: auto)

#let edgemsmcens = edge.with(marks: "-->", label-angle: auto)

#let dagnode = node.with(width: 1.1cm, height: 1.1cm)

#let Qbar(k) = $macron(Q)^g_(#k, tau)$
#let Qbarhat(k) = $hat(macron(Q))^g_(#k, tau)$
#let QbarL(k) = $macron(Q)^(g,-L)_(#k, tau)$
#let mean(k) = $bb(E)_#k$

#show: thmrules.with(qed-symbol: $square$)
#let unary(first, ..) = first
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"), base_level: 0)
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee"), base_level: 0)
#let assumption = thmbox("assumption", "Assumption", fill: rgb("#eeeeff"), base_level: 0)
#let definition = thmbox("definition", "Definition", fill: rgb("#ffeeee"), base_level: 0)
#let proof = thmproof("proof", "Proof")

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

#let timegrid(new_method: true) = {
    cetz.canvas(length: 1cm, {
        import cetz.draw: *

        set-style(
            mark: (fill: black, scale: 3),
            stroke: (thickness: 1.5pt, cap: "round"),
            angle: (
                radius: 0.3,
                label-radius: .8,
                fill: green.lighten(80%),
                stroke: (paint: green.darken(50%))
            ),
            content: (padding: 8pt)
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
            content("lend.start", [#text(size: 12pt)[$tau_"end"$]],anchor: "north")

            // Draw grid
            //for i in t_grid {
            //    line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
            //}

            // Deal with the marks/events
            let event_list = ()
            for t in range(0, time_values.len()) {
                event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
            }
            for v in event_list {
                line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
                if new_method {content(v.name + ".start", [#text(size: 12pt)[#v.mformat]], anchor: anchor)}
            }
        }
        let eventfun(x, where: "start", anchor: "north",start_y: 0)={
            let event_list = ()
            for t in range(0, x.len()) {
                event_list.push((name: "v" + str(t), value: x.at(t), mformat: $T_( #(t+1) )$))
            }
            for v in event_list {
                line((v.value, -1.5+start_y), (v.value, 1.5+start_y), stroke: blue,name: v.name)
                content(v.name + "." + where, [#text(size: 12pt)[#v.mformat]], anchor: anchor)
            }
        }
        let grid1 = (2.5,4.4,6.4)
        let grid2 = (1,1.7, 2.3,2.8)
        
        if new_method == false {
            rect((0,1.5), (2.8,-1.5),fill:aqua,stroke:none)
            
            eventfun(grid1)
            eventfun(grid2, where: "end", anchor: "south")
    
            group({time_grid((0,-1),(10,-1), grid1,anchor: "south")})
            group({time_grid((0,1),(10,1), grid2,anchor: "south")})
        } else {
            rect((0,1.5), (1.7,0.3),fill:aqua,stroke:none)
            rect((0,-1.7), (4.4,-0.5),fill:aqua,stroke:none)
    
            group({time_grid((0,-1),(10,-1), grid1, anchor: "north-east")})
            group({time_grid((0,1),(10,1), grid2, anchor: "north-east")})
        }
    })
}

#let prodint(s, t1, t2) = $product_(#s in (#t1, #t2])$
#let prodint2(s, t1, t2) = $product_(#s in (#t1, #t2))$
