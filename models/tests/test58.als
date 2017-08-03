module tests/test // Fancy sequence example written by Felix

abstract sig Obj { }

sig Name { }

sig File extends Obj { }

sig Dir extends Obj {
   map: Name->lone Obj,
   children: set Obj
}

one sig Root extends Dir { }

sig Path {
   names: seq Name,
   target: lone Obj,
   parent: lone Path
}

// This defines "Dir.children" based on the values of "Dir.map"
fact {
   all d:Dir | d.children = Name.(d.map)
}

// This defines "Path.target" and "Path.parent" based on the values of "Dir.map"
fact {
   all p:Path {
      (no p.names) => p.target=Root
      (one p.names) => p.target=Root.map[p.names.first]
      (!lone p.names) => p.target=(p.parent.target).map[p.names.last]
      (no p.names) => (no p.parent)
      (some p.names) => (one p.parent && p.names = p.parent.names + (#p.parent.names)->(p.names.last))
   }
}

// This makes more efficient use of the scope, by ensuring that any two distinct Path atoms will have distinct sequence of Names
fact {
   all p1, p2: Path | (p1.names=p2.names => p1=p2)
}

// This explicitly rejects any instance in which there is a cycle
fact {
   no x:Obj | x in x.^children
}

// This explicitly rejects any instance in which there is a File or Dir not reachable from Root
fact {
   all x:Obj | x in Root.*children
}

// Let's try to force a simulation of an interesting situation
run {
   some p:Path | no p.target
   some p1,p2:Path | { #(p1.names)=2 && #(p2.names)=2 && some p1.target && some p2.target && p1.target!=p2.target }
   some d:Dir | #(d.children)>1
} for 3 but 4 Obj, 7 Path expect 1
