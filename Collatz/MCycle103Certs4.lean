import Collatz.MCycle103Certs3

/-!
# Certificates of the listed shapes of `data103`, chunks 12..15
-/

set_option Elab.async false

namespace Collatz

theorem certs103_12 : certsOK 103 20 grid103 data103.certs shapes103_12 = true := by
  decide +kernel

theorem certs103_13 : certsOK 103 20 grid103 data103.certs shapes103_13 = true := by
  decide +kernel

theorem certs103_14 : certsOK 103 20 grid103 data103.certs shapes103_14 = true := by
  decide +kernel

theorem certs103_15 : certsOK 103 20 grid103 data103.certs shapes103_15 = true := by
  decide +kernel

end Collatz
