import Collatz.MCycle103Certs1

/-!
# Certificates of the listed shapes of `data103`, chunks 4..7
-/

set_option Elab.async false

namespace Collatz

theorem certs103_4 : certsOK 103 20 grid103 data103.certs shapes103_4 = true := by
  decide +kernel

theorem certs103_5 : certsOK 103 20 grid103 data103.certs shapes103_5 = true := by
  decide +kernel

theorem certs103_6 : certsOK 103 20 grid103 data103.certs shapes103_6 = true := by
  decide +kernel

theorem certs103_7 : certsOK 103 20 grid103 data103.certs shapes103_7 = true := by
  decide +kernel

end Collatz
