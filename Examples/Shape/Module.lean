import Examples.Shape.Program
import Project.Compiler.Command

namespace Examples.Shape

open Examples.Shape in
leanexe_compile shapes := [Shape.area, Shape.ofWords, Shape.scale, Shape.width, Shape.grow,
  Shape.normalize, totalArea]

end Examples.Shape
