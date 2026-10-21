import Collatz.MCycle103Certs2

/-!
# Certificates of the listed shapes of `data103`, chunks 8..11
-/

set_option Elab.async false

namespace Collatz

theorem certs103_8 : certsOK 103 20 grid103 data103.certs shapes103_8 = true := by
  decide +kernel

theorem certs103_9 : certsOK 103 20 grid103 data103.certs shapes103_9 = true := by
  decide +kernel

theorem certs103_10 : certsOK 103 20 grid103 data103.certs shapes103_10 = true := by
  decide +kernel

theorem certs103_11 : certsOK 103 20 grid103 data103.certs shapes103_11 = true := by
  decide +kernel

end Collatz
