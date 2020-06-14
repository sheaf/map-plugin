{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE RecordWildCards #-}

module MapPlugin ( plugin ) where

-- base
import Control.Arrow
  ( second )
import Control.Monad
  ( join )
import Data.Either
  ( partitionEithers )
import Data.Functor
  ( (<&>) )
import Data.Maybe
  ( catMaybes, fromMaybe )

-- ghc
import qualified GHC
    ( Module, mkModuleName )
import qualified GHC.Builtin.Types
  as GHC
    ( promotedNothingDataCon, promotedJustDataCon )
import qualified GHC.Builtin.Types.Prim
  as GHC
    ( eqPrimTyCon )
import qualified GHC.Core.Coercion
  as GHC
    ( mkUnivCo )
import qualified GHC.Core.DataCon
  as GHC
    ( promoteDataCon )
import qualified GHC.Core.Predicate
  as GHC
    ( Pred(..), classifyPredType
    , EqRel(..)
    )
import qualified GHC.Core.TyCo.Rep
  as GHC
    ( Type(..)
    , UnivCoProvenance(..)
    )
import qualified GHC.Core.Type
  as GHC
    ( mkTyConApp )
--import qualified GHC.Core.Unify
--  as GHC
--    ( tcMatchTyKi )
import qualified GHC.Driver.Finder
  as GHC
    ( FindResult(..) )
import qualified GHC.Data.FastString
  as GHC
    ( fsLit )
import qualified GHC.Plugins
  as GHC
    ( Plugin(..), defaultPlugin, purePlugin )
import qualified GHC.Core.DataCon
  as GHC
    ( DataCon )
import qualified GHC.Core.TyCon
  as GHC
    ( TyCon(..) )
import qualified GHC.Tc.Plugin
  as GHC
    ( findImportedModule
    , lookupOrig, tcLookupTyCon, tcLookupDataCon
    , newWanted
    )
import qualified GHC.Tc.Types
  as GHC
    ( TcPlugin(..)
    , TcPluginM
    , TcPluginResult(..)
    )
import qualified GHC.Tc.Types.Constraint
  as GHC
    ( Ct(..), ctPred
    , CtEvidence(..), ctEvidence
    , bumpCtLocDepth, mkNonCanonical
    )
import qualified GHC.Tc.Types.Evidence
  as GHC
    ( EvTerm, Role(..)
    , evCoercion
    )
import qualified GHC.Types.Name.Occurrence
  as GHC
    ( mkDataOcc, mkTcOcc )
import qualified GHC.Utils.Outputable
  as GHC
    ( ppr, pprTrace ) --, pprPanic )

--------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    }

tcPlugin :: [ String ] -> Maybe GHC.TcPlugin
tcPlugin _args =
  Just $
    GHC.TcPlugin
      { GHC.tcPluginInit  = tcPluginInit
      , GHC.tcPluginSolve = tcPluginSolve
      , GHC.tcPluginStop  = tcPluginStop
      }

data PluginDefs =
  PluginDefs
    { keyValTyCon     :: !GHC.TyCon
    , keyValDataCon   :: !GHC.DataCon
    , mapTyCon        :: !GHC.TyCon
    , fromListDataCon :: !GHC.DataCon
    , lookupTyCon     :: !GHC.TyCon
    , insertTyCon     :: !GHC.TyCon
    , deleteTyCon     :: !GHC.TyCon
    , unionTyCon      :: !GHC.TyCon
    , differenceTyCon :: !GHC.TyCon
    }

tcPluginInit :: GHC.TcPluginM PluginDefs
tcPluginInit = do
  dataTypeMapModule <- findModule "Map-Plugin" "Data.Type.Map"
  keyValTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   ":->"        )
  keyValDataCon   <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc ":->"        )
  mapTyCon        <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Map"        )
  fromListDataCon <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc "FromList"   )
  lookupTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Lookup"     )
  insertTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Insert"     )
  deleteTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Delete"     )
  unionTyCon      <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Union"      )
  differenceTyCon <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Difference" )
  pure ( PluginDefs { .. } )

findModule :: String -> String -> GHC.TcPluginM GHC.Module
findModule pkg modName = do
  findResult <- GHC.findImportedModule ( GHC.mkModuleName modName ) ( Just $ GHC.fsLit pkg )
  case findResult of
    GHC.Found _ res     -> pure res
    GHC.FoundMultiple _ -> error $ "MapPlugin: found multiple modules named " <> modName <> "."
    _                   -> error $ "MapPlugin: could not find any module named " <> modName <> "."

tcPluginStop :: PluginDefs -> GHC.TcPluginM ()
tcPluginStop _ = pure ()

tcPluginSolve :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.TcPluginM GHC.TcPluginResult
tcPluginSolve _state _givens _deriveds []      = pure $ GHC.TcPluginOk [] []
tcPluginSolve  state  givens  deriveds wanteds = do
  ( contras, oks )
    <- GHC.pprTrace "Givens:"   ( GHC.ppr givens   )
    .  GHC.pprTrace "Deriveds:" ( GHC.ppr deriveds )
    .  GHC.pprTrace "Wanteds:"  ( GHC.ppr wanteds  )
    .  partitionEithers
    .  catMaybes
    <$> traverse ( \ wanted -> specifyWanted wanted <$> solveWanted state givens deriveds wanted ) wanteds
  case contras of
    [] ->
      let
        solveds :: [ ( GHC.EvTerm, GHC.Ct ) ]
        news    :: [ GHC.Ct ]
        ( solveds, news ) = second join ( unzip oks )
      in  pure $ GHC.TcPluginOk solveds news
    _  -> pure $ GHC.TcPluginContradiction contras

data SolverResult
  = Ignore
  | Solved
    { evidence   :: !GHC.EvTerm
    , newWanteds :: ![ GHC.Ct ]
    }
  | Contradiction

specifyWanted :: GHC.Ct -> SolverResult -> Maybe ( Either GHC.Ct ( ( GHC.EvTerm, GHC.Ct ), [ GHC.Ct ] ) )
specifyWanted _      Ignore            = Nothing
specifyWanted wanted ( Solved { .. } ) = Just ( Right ( ( evidence, wanted ), newWanteds ) )
specifyWanted wanted Contradiction     = Just ( Left wanted )

solveWanted :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.Ct -> GHC.TcPluginM SolverResult
solveWanted pluginDefs givens _deriveds wanted =
  let
    wantedEv :: GHC.CtEvidence
    wantedEv = GHC.ctEvidence wanted
  in
    case GHC.classifyPredType ( GHC.ctPred wanted ) of
      GHC.EqPred GHC.NomEq lhs rhs -> do
        mbLhs' <- simplify pluginDefs givens lhs
        mbRhs' <- simplify pluginDefs givens rhs
        case ( mbLhs', mbRhs' ) of
          -- No simplifications achieved.
          ( Nothing, Nothing ) -> pure Ignore
          -- Some simplification achieved.
          _ -> do
            let
              -- Evidence for the old wanted (that we are now declaring to be solved).
              evidence :: GHC.EvTerm
              evidence = GHC.evCoercion $ GHC.mkUnivCo ( GHC.PluginProv "Map-Plugin" ) GHC.Nominal lhs rhs
              lhs', rhs' :: GHC.Type
              lhs' = fromMaybe lhs mbLhs'
              rhs' = fromMaybe rhs mbRhs'
            newWanted <-
              GHC.mkNonCanonical <$>
                GHC.newWanted
                  ( GHC.bumpCtLocDepth $ GHC.ctev_loc wantedEv )
                  ( GHC.mkTyConApp GHC.eqPrimTyCon [ lhs', rhs' ] )
            pure $ Solved { evidence, newWanteds = [ newWanted ] }
      _ -> pure Ignore

-- | Try to simplify a type, e.g. simplify @ Lookup k ( Insert k v s ) @ to @ v @.
simplify :: PluginDefs -> [ GHC.Ct ] -> GHC.Type -> GHC.TcPluginM ( Maybe GHC.Type )
simplify pluginDefs@( PluginDefs { .. } ) givens ty =
  case ty of
    -- Recognise one of the handled `TyCon`s (`Lookup`, `Insert`, ...)
    GHC.TyConApp tyCon args
      -- Fully saturated application of `Lookup` type family
      | tyCon == lookupTyCon
      , [ _kind_k, _kind_v, k, kvs ] <- args
      -> isElement pluginDefs givens k kvs
      <&> fmap \case
        Absent    -> GHC.TyConApp GHC.promotedNothingDataCon []
        Present v -> GHC.TyConApp GHC.promotedJustDataCon    [ v ]
    _ -> pure Nothing

-- | Whether an element is present or absent in a map.
data Element
  = Absent
  | Present GHC.Type

-- | Tries to deduce whether the specified key occurs in a map.
--
-- Returns @Nothing@ when there isn't enough information available to know.
isElement :: PluginDefs -> [ GHC.Ct ] -> GHC.Type -> GHC.Type -> GHC.TcPluginM ( Maybe Element )
isElement pluginDefs@( PluginDefs { .. } ) givens k0 kvs0 =
  case kvs0 of
    GHC.TyConApp tyCon args
      | tyCon == insertTyCon
      , [ _kind_k, _kind_v, k1, v1, kvs1 ] <- args
      -> do
        mbEq <- eqTy pluginDefs givens k0 k1
        case mbEq of
          Nothing -> do
            isElemFurther <- isElement pluginDefs givens k0 kvs1
            case isElemFurther of
              Just ( Present _ ) -> pure isElemFurther -- TODO: emit apartness constraint
              _                  -> pure Nothing
          Just True ->
            pure ( Just $ Present v1 )
          Just False ->
            isElement pluginDefs givens k0 kvs1
      | tyCon == deleteTyCon
      , [ _kind_k, _kind_v, k1, kvs1 ] <- args
      -> do
        mbEq <- eqTy pluginDefs givens k0 k1
        case mbEq of
          Nothing    -> pure Nothing
          Just True  -> pure ( Just Absent )
          Just False -> isElement pluginDefs givens k0 kvs1
      | tyCon == GHC.promoteDataCon fromListDataCon
      , [ _kind_k, _kind_v, list ] <- args
      -> isListElement pluginDefs givens k0 list
    _ -> pure Nothing

-- | Checks whether a key occurs in a type-level list.
isListElement :: PluginDefs -> [ GHC.Ct ] -> GHC.Type -> GHC.Type -> GHC.TcPluginM ( Maybe Element )
isListElement ( PluginDefs {} ) _givens _k _list = pure Nothing -- TODO

-- | Computes whether `lhs == rhs`.
--
--  - @ Just True @: types are equal,
--  - @ Just False @: types are apart,
--  - @ Nothing @: unknown at this stage.
eqTy :: PluginDefs -> [ GHC.Ct ] -> GHC.Type -> GHC.Type -> GHC.TcPluginM ( Maybe Bool )
eqTy ( PluginDefs {} ) _givens _lhs _rhs = pure Nothing -- TODO
