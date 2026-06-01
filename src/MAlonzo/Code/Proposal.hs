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

module MAlonzo.Code.Proposal where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.Data.Rational.Base

-- Proposal.Proposal
d_Proposal_2 = ()
data T_Proposal_2
  = C_constructor_16 Integer MAlonzo.Code.Data.Rational.Base.T_ℚ_6
                     MAlonzo.Code.Agent.T_Role_2
-- Proposal.Proposal.proposer
d_proposer_10 :: T_Proposal_2 -> Integer
d_proposer_10 v0
  = case coe v0 of
      C_constructor_16 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Proposal.Proposal.price
d_price_12 :: T_Proposal_2 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_price_12 v0
  = case coe v0 of
      C_constructor_16 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Proposal.Proposal.role
d_role_14 :: T_Proposal_2 -> MAlonzo.Code.Agent.T_Role_2
d_role_14 v0
  = case coe v0 of
      C_constructor_16 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Proposal.L0Constraint
d_L0Constraint_18 ::
  MAlonzo.Code.Agent.T_Agent_18 -> T_Proposal_2 -> ()
d_L0Constraint_18 = erased
-- Proposal.L3Constraint
d_L3Constraint_20 ::
  MAlonzo.Code.Agent.T_Agent_18 -> T_Proposal_2 -> ()
d_L3Constraint_20 = erased
-- Proposal._.v
d_v_30 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  T_Proposal_2 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_v_30 v0 ~v1 = du_v_30 v0
du_v_30 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_v_30 v0
  = coe
      MAlonzo.Code.Agent.d_unitValue_12
      (coe MAlonzo.Code.Agent.d_valuation_34 (coe v0))
-- Proposal._.p
d_p_32 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  T_Proposal_2 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_p_32 ~v0 v1 = du_p_32 v1
du_p_32 :: T_Proposal_2 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_p_32 v0 = coe d_price_12 (coe v0)
-- Proposal._.b
d_b_34 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  T_Proposal_2 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_b_34 v0 ~v1 = du_b_34 v0
du_b_34 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_b_34 v0 = coe MAlonzo.Code.Agent.d_budget_36 (coe v0)
-- Proposal._.n
d_n_36 :: MAlonzo.Code.Agent.T_Agent_18 -> T_Proposal_2 -> Integer
d_n_36 v0 ~v1 = du_n_36 v0
du_n_36 :: MAlonzo.Code.Agent.T_Agent_18 -> Integer
du_n_36 v0 = coe MAlonzo.Code.Agent.d_inventory_38 (coe v0)
-- Proposal._.go
d_go_38 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  T_Proposal_2 -> MAlonzo.Code.Agent.T_Role_2 -> ()
d_go_38 = erased
