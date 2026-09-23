import type * as __compactRuntime from '@midnight-ntwrk/compact-runtime';

export type Witnesses<PS> = {
}

export type ImpureCircuits<PS> = {
  wFirst(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
  bump(context: __compactRuntime.CircuitContext<PS>): Promise<__compactRuntime.CircuitResults<PS, []>>;
  credit(context: __compactRuntime.CircuitContext<PS>, k_0: bigint, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type ProvableCircuits<PS> = {
  wFirst(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
  bump(context: __compactRuntime.CircuitContext<PS>): Promise<__compactRuntime.CircuitResults<PS, []>>;
  credit(context: __compactRuntime.CircuitContext<PS>, k_0: bigint, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type PureCircuits = {
}

export type Circuits<PS> = {
  wFirst(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
  bump(context: __compactRuntime.CircuitContext<PS>): Promise<__compactRuntime.CircuitResults<PS, []>>;
  credit(context: __compactRuntime.CircuitContext<PS>, k_0: bigint, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
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
  f14: {
    isEmpty(): boolean;
    size(): bigint;
    member(key_0: bigint): boolean;
    lookup(key_0: bigint): bigint;
    [Symbol.iterator](): Iterator<[bigint, bigint]>
  };
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
