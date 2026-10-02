import LeanExe.Examples.Shape
import Project.Compiler.Command

namespace Project.Shape

open LeanExe.Examples.Shape in
leanexe_compile shapes := [Shape.area, Shape.ofWords, Shape.scale, Shape.width, Shape.grow,
  Shape.normalize, totalArea]

end Project.Shape
