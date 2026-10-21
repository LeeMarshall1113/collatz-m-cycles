import Collatz.MCycle103Certs4

/-!
# Certificates of the listed shapes of `data103`, chunks 16..19
-/

set_option Elab.async false

namespace Collatz

theorem certs103_16 : certsOK 103 20 grid103 data103.certs shapes103_16 = true := by
  decide +kernel

theorem certs103_17 : certsOK 103 20 grid103 data103.certs shapes103_17 = true := by
  decide +kernel

theorem certs103_18 : certsOK 103 20 grid103 data103.certs shapes103_18 = true := by
  decide +kernel

theorem certs103_19 : certsOK 103 20 grid103 data103.certs shapes103_19 = true := by
  decide +kernel

end Collatz
