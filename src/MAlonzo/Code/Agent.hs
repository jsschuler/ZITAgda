{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Agent where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Rational.Base

-- Agent.Role
d_Role_2 = ()
data T_Role_2 = C_Buyer_4 | C_Seller_6
-- Agent.ValuationSchedule
d_ValuationSchedule_8 = ()
newtype T_ValuationSchedule_8
  = C_constructor_14 MAlonzo.Code.Data.Rational.Base.T_ℚ_6
-- Agent.ValuationSchedule.unitValue
d_unitValue_12 ::
  T_ValuationSchedule_8 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_unitValue_12 v0
  = case coe v0 of
      C_constructor_14 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Agent.TraderId
d_TraderId_16 :: ()
d_TraderId_16 = erased
-- Agent.Agent
d_Agent_18 = ()
data T_Agent_18
  = C_constructor_40 Integer T_Role_2 T_ValuationSchedule_8
                     MAlonzo.Code.Data.Rational.Base.T_ℚ_6 Integer
-- Agent.Agent.id
d_id_30 :: T_Agent_18 -> Integer
d_id_30 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Agent.Agent.role
d_role_32 :: T_Agent_18 -> T_Role_2
d_role_32 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Agent.Agent.valuation
d_valuation_34 :: T_Agent_18 -> T_ValuationSchedule_8
d_valuation_34 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Agent.Agent.budget
d_budget_36 :: T_Agent_18 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_budget_36 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Agent.Agent.inventory
d_inventory_38 :: T_Agent_18 -> Integer
d_inventory_38 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
