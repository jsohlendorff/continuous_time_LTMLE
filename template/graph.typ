#import "@preview/fletcher:0.5.7" as fletcher: node, edge, diagram
#import "@preview/cetz:0.3.4"
#import "@preview/touying:0.6.1": *

#let edgemsm = edge.with(marks: "->", label-angle: auto)
#let edgemsmcens = edge.with(marks: "-->", label-angle: auto)
#let dagnode = node.with(width: 1.1cm, height: 1.1cm)

// cetz and fletcher bindings for touying
#let cetz-canvas = touying-reducer.with(reduce: cetz.canvas, cover: cetz.draw.hide.with(bounds: true))
#let fletcher-diagram = touying-reducer.with(reduce: fletcher.diagram, cover: fletcher.hide)

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

#let timegrid(new_method: true, slides: false) = {
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
            
            if slides == true {
                (pause, )
            }
            
            eventfun(grid1)
            eventfun(grid2, where: "end", anchor: "south")

            group({time_grid((0,-1),(10,-1), grid1,anchor: "south")})
            group({time_grid((0,1),(10,1), grid2,anchor: "south")})
        } else {
            rect((0,1.5), (1.7,0.3),fill:aqua,stroke:none)
            rect((0,-1.7), (4.4,-0.5),fill:aqua,stroke:none)

            if slides == true {
                    (pause,)
            }
            
            group({time_grid((0,-1),(10,-1), grid1, anchor: "north-east")})
            group({time_grid((0,1),(10,1), grid2, anchor: "north-east")})
        }
    })
}

