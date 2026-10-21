import Collatz.MCycle103Shapes

/-!
# Certificates of the listed shapes of `data103`, chunks 0..3
-/

set_option Elab.async false

namespace Collatz

theorem certs103_0 : certsOK 103 20 grid103 data103.certs shapes103_0 = true := by
  decide +kernel

theorem certs103_1 : certsOK 103 20 grid103 data103.certs shapes103_1 = true := by
  decide +kernel

theorem certs103_2 : certsOK 103 20 grid103 data103.certs shapes103_2 = true := by
  decide +kernel

theorem certs103_3 : certsOK 103 20 grid103 data103.certs shapes103_3 = true := by
  decide +kernel

end Collatz
