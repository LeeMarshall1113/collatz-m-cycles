import Collatz.MCycle104Certs2

/-!
# Certificates of the listed shapes of `data104`, chunks 8..11
-/

set_option Elab.async false

namespace Collatz

theorem certs104_8 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_8 = true := by
  decide +kernel

theorem certs104_9 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_9 = true := by
  decide +kernel

theorem certs104_10 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_10 = true := by
  decide +kernel

theorem certs104_11 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_11 = true := by
  decide +kernel

end Collatz
