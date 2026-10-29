import Library.Sorting.Insertion.Program
import Verified.Reflect.Command

namespace Library.Sorting.Insertion

set_option verified_compile.alignedNative true in
verified_compile compiled := [sortInsert]

end Library.Sorting.Insertion
