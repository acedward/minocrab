import type * as __compactRuntime from '@midnight-ntwrk/compact-runtime';

export type Witnesses<PS> = {
}

export type ImpureCircuits<PS> = {
  wLast(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type ProvableCircuits<PS> = {
  wLast(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type PureCircuits = {
}

export type Circuits<PS> = {
  wLast(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type Ledger = {
  readonly magic: Uint8Array;
  readonly f1: bigint;
  readonly f2: bigint;
  readonly f3: bigint;
  readonly f4: bigint;
  readonly f5: bigint;
  readonly f6: bigint;
  readonly f7: bigint;
  readonly f8: bigint;
  readonly f9: bigint;
  readonly f10: bigint;
  readonly f11: bigint;
  readonly f12: bigint;
  readonly f13: bigint;
  readonly f14: bigint;
  readonly f15: bigint;
}

export type ContractReferenceLocations = any;

export declare const contractReferenceLocations : ContractReferenceLocations;

export declare class Contract<PS = any, W extends Witnesses<PS> = Witnesses<PS>> {
  witnesses: W;
  circuits: Circuits<PS>;
  impureCircuits: ImpureCircuits<PS>;
  provableCircuits: ProvableCircuits<PS>;
  constructor(witnesses: W);
  initialState(context: __compactRuntime.ConstructorContext<PS>): Promise<__compactRuntime.ConstructorResult<PS>>;
}

export declare function ledger(state: __compactRuntime.StateValue | __compactRuntime.ChargedState): Ledger;
export declare const pureCircuits: PureCircuits;
export declare const expectedVk: Record<string, string>;
