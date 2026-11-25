import KWPartition
import Mathlib.Data.Fintype.Pi
import G11Game
namespace G11Game
open KWPartition
def star : Formula (Fin 11) := (.join (.join (.join (.join (.join (.join (.meet (.var 0) (.join (.var 9) (.var 10))) (.meet (.var 4) (.join (.join (.var 1) (.var 8)) (.var 10)))) (.meet (.var 8) (.join (.var 1) (.var 9)))) (.meet (.var 2) (.join (.var 5) (.var 10)))) (.meet (.var 6) (.join (.join (.var 3) (.var 7)) (.var 10)))) (.meet (.var 7) (.join (.var 3) (.var 9)))) (.meet (.var 5) (.join (.var 8) (.var 9))))
theorem star_size : star.gates = 22 := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem star_correct : ∀ x : Fin 11 → Bool, star.eval x = graph x := by decide +kernel
end G11Game
