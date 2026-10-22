import Collatz.MCycle104Certs1

/-!
# Certificates of the listed shapes of `data104`, chunks 4..7
-/

set_option Elab.async false

namespace Collatz

theorem certs104_4 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_4 = true := by
  decide +kernel

theorem certs104_5 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_5 = true := by
  decide +kernel

theorem certs104_6 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_6 = true := by
  decide +kernel

theorem certs104_7 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_7 = true := by
  decide +kernel

end Collatz
