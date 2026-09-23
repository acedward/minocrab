import type * as __compactRuntime from '@midnight-ntwrk/compact-runtime';

export type Witnesses<PS> = {
}

export type ImpureCircuits<PS> = {
  setValue(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
  bump(context: __compactRuntime.CircuitContext<PS>): Promise<__compactRuntime.CircuitResults<PS, []>>;
  credit(context: __compactRuntime.CircuitContext<PS>,
         k_0: Uint8Array,
         v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type ProvableCircuits<PS> = {
  setValue(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
  bump(context: __compactRuntime.CircuitContext<PS>): Promise<__compactRuntime.CircuitResults<PS, []>>;
  credit(context: __compactRuntime.CircuitContext<PS>,
         k_0: Uint8Array,
         v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type PureCircuits = {
}

export type Circuits<PS> = {
  setValue(context: __compactRuntime.CircuitContext<PS>, v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
  bump(context: __compactRuntime.CircuitContext<PS>): Promise<__compactRuntime.CircuitResults<PS, []>>;
  credit(context: __compactRuntime.CircuitContext<PS>,
         k_0: Uint8Array,
         v_0: bigint): Promise<__compactRuntime.CircuitResults<PS, []>>;
}

export type Ledger = {
  readonly magic: Uint8Array;
  readonly value: bigint;
  readonly count: bigint;
  balances: {
    isEmpty(): boolean;
    size(): bigint;
    member(key_0: Uint8Array): boolean;
    lookup(key_0: Uint8Array): bigint;
    [Symbol.iterator](): Iterator<[Uint8Array, bigint]>
  };
  readonly owner: Uint8Array;
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
