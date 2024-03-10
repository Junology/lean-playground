-- This module serves as the root of the `LeanPlayground` library.
-- Import modules here that should be built as part of the library.
import «LeanPlayground».Basic
import «LeanPlayground».Server
import «LeanPlayground».Extension

def test : Prop := False

/-- error: 'test' has already been declared -/
#guard_msgs in def test : Prop := False
