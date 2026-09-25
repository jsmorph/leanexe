module

public import Init.System.IO
import all Init.System.IO
import all Init.System.ST

public section

namespace Project.RunningSum.Source

theorem pure_apply (value : α) (world : Void IO.RealWorld) :
    (pure value : BaseIO α) world = ⟨value, world⟩ := (rfl)

theorem bind_apply (action : BaseIO α) (next : α → BaseIO β) (world : Void IO.RealWorld) :
    (action >>= next) world = next (action world).val (action world).state := (rfl)

end Project.RunningSum.Source
