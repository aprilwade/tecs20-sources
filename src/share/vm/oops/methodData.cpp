/*
 * Copyright (c) 2000, 2016, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */


#include "precompiled.hpp"
#include "classfile/systemDictionary.hpp"
#include "compiler/compilerOracle.hpp"
#include "interpreter/bytecode.hpp"
#include "interpreter/bytecodeStream.hpp"
#include "interpreter/linkResolver.hpp"
#include "memory/heapInspection.hpp"
#include "memory/resourceArea.hpp"
#include "oops/methodData.hpp"
#include "prims/jvmtiRedefineClasses.hpp"
#include "runtime/arguments.hpp"
#include "runtime/compilationPolicy.hpp"
#include "runtime/deoptimization.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/orderAccess.inline.hpp"
#include "utilities/copy.hpp"

// ==================================================================
// DataLayout
//
// Overlay for generic profiling data.

// Some types of data layouts need a length field.
bool DataLayout::needs_array_len(u1 tag) {
  return (tag == multi_branch_data_tag) || (tag == arg_info_data_tag) || (tag == parameters_type_data_tag);
}

// Perform generic initialization of the data.  More specific
// initialization occurs in overrides of ProfileData::post_initialize.
void DataLayout::initialize(u1 tag, u2 bci, int cell_count) {
  _header._bits = (intptr_t)0;
  _header._struct._tag = tag;
  _header._struct._bci = bci;
  for (int i = 0; i < cell_count; i++) {
    set_cell_at(i, (intptr_t)0);
  }
  if (needs_array_len(tag)) {
    set_cell_at(ArrayData::array_len_off_set, cell_count - 1); // -1 for header.
  }
  if (tag == call_type_data_tag) {
    CallTypeData::initialize(this, cell_count);
  } else if (tag == virtual_call_type_data_tag) {
    VirtualCallTypeData::initialize(this, cell_count);
  }
}

void DataLayout::clean_weak_klass_links(BoolObjectClosure* cl) {
  ResourceMark m;
  data_in()->clean_weak_klass_links(cl);
}


// ==================================================================
// ProfileData
//
// A ProfileData object is created to refer to a section of profiling
// data in a structured way.

// Constructor for invalid ProfileData.
ProfileData::ProfileData() {
  _data = NULL;
}

char* ProfileData::print_data_on_helper(const MethodData* md) const {
  DataLayout* dp  = md->extra_data_base();
  DataLayout* end = md->args_data_limit();
  stringStream ss;
  for (;; dp = MethodData::next_extra(dp)) {
    assert(dp < end, "moved past end of extra data");
    switch(dp->tag()) {
    case DataLayout::speculative_trap_data_tag:
      if (dp->bci() == bci()) {
        SpeculativeTrapData* data = new SpeculativeTrapData(dp);
        int trap = data->trap_state();
        char buf[100];
        ss.print("trap/");
        data->method()->print_short_name(&ss);
        ss.print("(%s) ", Deoptimization::format_trap_state(buf, sizeof(buf), trap));
      }
      break;
    case DataLayout::bit_data_tag:
      break;
    case DataLayout::no_tag:
    case DataLayout::arg_info_data_tag:
      return ss.as_string();
      break;
    default:
      fatal("unexpected tag %d", dp->tag());
    }
  }
  return NULL;
}

void ProfileData::print_data_on(outputStream* st, const MethodData* md) const {
  print_data_on(st, print_data_on_helper(md));
}

void ProfileData::print_shared(outputStream* st, const char* name, const char* extra) const {
  st->print("bci: %d", bci());
  st->fill_to(tab_width_one);
  st->print("%s", name);
  tab(st);
  int trap = trap_state();
  if (trap != 0) {
    char buf[100];
    st->print("trap(%s) ", Deoptimization::format_trap_state(buf, sizeof(buf), trap));
  }
  if (extra != NULL) {
    st->print("%s", extra);
  }
  int flags = data()->flags();
  if (flags != 0) {
    st->print("flags(%d) ", flags);
  }
}

void ProfileData::tab(outputStream* st, bool first) const {
  st->fill_to(first ? tab_width_one : tab_width_two);
}

// ==================================================================
// BitData
//
// A BitData corresponds to a one-bit flag.  This is used to indicate
// whether a checkcast bytecode has seen a null value.


void BitData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "BitData", extra);
  st->cr();
}

// ==================================================================
// CounterData
//
// A CounterData corresponds to a simple counter.

void CounterData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "CounterData", extra);
  st->print_cr("count(%u)", count());
}

// ==================================================================
// JumpData
//
// A JumpData is used to access profiling information for a direct
// branch.  It is a counter, used for counting the number of branches,
// plus a data displacement, used for realigning the data pointer to
// the corresponding target bci.

void JumpData::post_initialize(BytecodeStream* stream, MethodData* mdo) {
  assert(stream->bci() == bci(), "wrong pos");
  int target;
  Bytecodes::Code c = stream->code();
  if (c == Bytecodes::_goto_w || c == Bytecodes::_jsr_w) {
    target = stream->dest_w();
  } else {
    target = stream->dest();
  }
  int my_di = mdo->dp_to_di(dp());
  int target_di = mdo->bci_to_di(target);
  int offset = target_di - my_di;
  set_displacement(offset);
}

void JumpData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "JumpData", extra);
  st->print_cr("taken(%u) displacement(%d)", taken(), displacement());
}

int TypeStackSlotEntries::compute_cell_count(Symbol* signature, bool include_receiver, int max) {
  // Parameter profiling include the receiver
  int args_count = include_receiver ? 1 : 0;
  ResourceMark rm;
  SignatureStream ss(signature);
  args_count += ss.reference_parameter_count();
  args_count = MIN2(args_count, max);
  return args_count * per_arg_cell_count;
}

int TypeEntriesAtCall::compute_cell_count(BytecodeStream* stream) {
  assert(Bytecodes::is_invoke(stream->code()), "should be invoke");
  assert(TypeStackSlotEntries::per_arg_count() > ReturnTypeEntry::static_cell_count(), "code to test for arguments/results broken");
  Bytecode_invoke inv(stream->method(), stream->bci());
  int args_cell = 0;
  if (arguments_profiling_enabled()) {
    args_cell = TypeStackSlotEntries::compute_cell_count(inv.signature(), false, TypeProfileArgsLimit);
  }
  int ret_cell = 0;
  if (return_profiling_enabled() && (inv.result_type() == T_OBJECT || inv.result_type() == T_ARRAY)) {
    ret_cell = ReturnTypeEntry::static_cell_count();
  }
  int header_cell = 0;
  if (args_cell + ret_cell > 0) {
    header_cell = header_cell_count();
  }

  return header_cell + args_cell + ret_cell;
}

class ArgumentOffsetComputer : public SignatureInfo {
private:
  int _max;
  GrowableArray<int> _offsets;

  void set(int size, BasicType type) { _size += size; }
  void do_object(int begin, int end) {
    if (_offsets.length() < _max) {
      _offsets.push(_size);
    }
    SignatureInfo::do_object(begin, end);
  }
  void do_array (int begin, int end) {
    if (_offsets.length() < _max) {
      _offsets.push(_size);
    }
    SignatureInfo::do_array(begin, end);
  }

public:
  ArgumentOffsetComputer(Symbol* signature, int max)
    : SignatureInfo(signature), _max(max), _offsets(Thread::current(), max) {
  }

  int total() { lazy_iterate_parameters(); return _size; }

  int off_at(int i) const { return _offsets.at(i); }
};

void TypeStackSlotEntries::post_initialize(Symbol* signature, bool has_receiver, bool include_receiver) {
  ResourceMark rm;
  int start = 0;
  // Parameter profiling include the receiver
  if (include_receiver && has_receiver) {
    set_stack_slot(0, 0);
    set_type(0, type_none());
    start += 1;
  }
  ArgumentOffsetComputer aos(signature, _number_of_entries-start);
  aos.total();
  for (int i = start; i < _number_of_entries; i++) {
    set_stack_slot(i, aos.off_at(i-start) + (has_receiver ? 1 : 0));
    set_type(i, type_none());
  }
}

void CallTypeData::post_initialize(BytecodeStream* stream, MethodData* mdo) {
  assert(Bytecodes::is_invoke(stream->code()), "should be invoke");
  Bytecode_invoke inv(stream->method(), stream->bci());

  SignatureStream ss(inv.signature());
  if (has_arguments()) {
#ifdef ASSERT
    ResourceMark rm;
    int count = MIN2(ss.reference_parameter_count(), (int)TypeProfileArgsLimit);
    assert(count > 0, "room for args type but none found?");
    check_number_of_arguments(count);
#endif
    _args.post_initialize(inv.signature(), inv.has_receiver(), false);
  }

  if (has_return()) {
    assert(inv.result_type() == T_OBJECT || inv.result_type() == T_ARRAY, "room for a ret type but doesn't return obj?");
    _ret.post_initialize();
  }
}

void VirtualCallTypeData::post_initialize(BytecodeStream* stream, MethodData* mdo) {
  assert(Bytecodes::is_invoke(stream->code()), "should be invoke");
  Bytecode_invoke inv(stream->method(), stream->bci());

  if (has_arguments()) {
#ifdef ASSERT
    ResourceMark rm;
    SignatureStream ss(inv.signature());
    int count = MIN2(ss.reference_parameter_count(), (int)TypeProfileArgsLimit);
    assert(count > 0, "room for args type but none found?");
    check_number_of_arguments(count);
#endif
    _args.post_initialize(inv.signature(), inv.has_receiver(), false);
  }

  if (has_return()) {
    assert(inv.result_type() == T_OBJECT || inv.result_type() == T_ARRAY, "room for a ret type but doesn't return obj?");
    _ret.post_initialize();
  }
}

bool TypeEntries::is_loader_alive(BoolObjectClosure* is_alive_cl, intptr_t p) {
  Klass* k = (Klass*)klass_part(p);
  return k != NULL && k->is_loader_alive(is_alive_cl);
}

void TypeStackSlotEntries::clean_weak_klass_links(BoolObjectClosure* is_alive_cl) {
  for (int i = 0; i < _number_of_entries; i++) {
    intptr_t p = type(i);
    if (!is_loader_alive(is_alive_cl, p)) {
      set_type(i, with_status((Klass*)NULL, p));
    }
  }
}

void ReturnTypeEntry::clean_weak_klass_links(BoolObjectClosure* is_alive_cl) {
  intptr_t p = type();
  if (!is_loader_alive(is_alive_cl, p)) {
    set_type(with_status((Klass*)NULL, p));
  }
}

bool TypeEntriesAtCall::return_profiling_enabled() {
  return MethodData::profile_return();
}

bool TypeEntriesAtCall::arguments_profiling_enabled() {
  return MethodData::profile_arguments();
}

void TypeEntries::print_klass(outputStream* st, intptr_t k) {
  if (is_type_none(k)) {
    st->print("none");
  } else if (is_type_unknown(k)) {
    st->print("unknown");
  } else {
    valid_klass(k)->print_value_on(st);
  }
  if (was_null_seen(k)) {
    st->print(" (null seen)");
  }
}

void TypeStackSlotEntries::print_data_on(outputStream* st) const {
  for (int i = 0; i < _number_of_entries; i++) {
    _pd->tab(st);
    st->print("%d: stack(%u) ", i, stack_slot(i));
    print_klass(st, type(i));
    st->cr();
  }
}

void ReturnTypeEntry::print_data_on(outputStream* st) const {
  _pd->tab(st);
  print_klass(st, type());
  st->cr();
}

void CallTypeData::print_data_on(outputStream* st, const char* extra) const {
  CounterData::print_data_on(st, extra);
  if (has_arguments()) {
    tab(st, true);
    st->print("argument types");
    _args.print_data_on(st);
  }
  if (has_return()) {
    tab(st, true);
    st->print("return type");
    _ret.print_data_on(st);
  }
}

void VirtualCallTypeData::print_data_on(outputStream* st, const char* extra) const {
  VirtualCallData::print_data_on(st, extra);
  if (has_arguments()) {
    tab(st, true);
    st->print("argument types");
    _args.print_data_on(st);
  }
  if (has_return()) {
    tab(st, true);
    st->print("return type");
    _ret.print_data_on(st);
  }
}

// ==================================================================
// ReceiverTypeData
//
// A ReceiverTypeData is used to access profiling information about a
// dynamic type check.  It consists of a counter which counts the total times
// that the check is reached, and a series of (Klass*, count) pairs
// which are used to store a type profile for the receiver of the check.

void ReceiverTypeData::clean_weak_klass_links(BoolObjectClosure* is_alive_cl) {
    for (uint row = 0; row < row_limit(); row++) {
    Klass* p = receiver(row);
    if (p != NULL && !p->is_loader_alive(is_alive_cl)) {
      clear_row(row);
    }
  }
}

#if INCLUDE_JVMCI
void VirtualCallData::clean_weak_klass_links(BoolObjectClosure* is_alive_cl) {
  ReceiverTypeData::clean_weak_klass_links(is_alive_cl);
  for (uint row = 0; row < method_row_limit(); row++) {
    Method* p = method(row);
    if (p != NULL && !p->method_holder()->is_loader_alive(is_alive_cl)) {
      clear_method_row(row);
    }
  }
}

void VirtualCallData::clean_weak_method_links() {
  ReceiverTypeData::clean_weak_method_links();
  for (uint row = 0; row < method_row_limit(); row++) {
    Method* p = method(row);
    if (p != NULL && !p->on_stack()) {
      clear_method_row(row);
    }
  }
}
#endif // INCLUDE_JVMCI

void ReceiverTypeData::print_receiver_data_on(outputStream* st) const {
  uint row;
  int entries = 0;
  for (row = 0; row < row_limit(); row++) {
    if (receiver(row) != NULL)  entries++;
  }
#if INCLUDE_JVMCI
  st->print_cr("count(%u) nonprofiled_count(%u) entries(%u)", count(), nonprofiled_count(), entries);
#else
  st->print_cr("count(%u) entries(%u)", count(), entries);
#endif
  int total = count();
  for (row = 0; row < row_limit(); row++) {
    if (receiver(row) != NULL) {
      total += receiver_count(row);
    }
  }
  for (row = 0; row < row_limit(); row++) {
    if (receiver(row) != NULL) {
      tab(st);
      receiver(row)->print_value_on(st);
      st->print_cr("(%u %4.2f)", receiver_count(row), (float) receiver_count(row) / (float) total);
    }
  }
}
void ReceiverTypeData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "ReceiverTypeData", extra);
  print_receiver_data_on(st);
}

#if INCLUDE_JVMCI
void VirtualCallData::print_method_data_on(outputStream* st) const {
  uint row;
  int entries = 0;
  for (row = 0; row < method_row_limit(); row++) {
    if (method(row) != NULL) entries++;
  }
  tab(st);
  st->print_cr("method_entries(%u)", entries);
  int total = count();
  for (row = 0; row < method_row_limit(); row++) {
    if (method(row) != NULL) {
      total += method_count(row);
    }
  }
  for (row = 0; row < method_row_limit(); row++) {
    if (method(row) != NULL) {
      tab(st);
      method(row)->print_value_on(st);
      st->print_cr("(%u %4.2f)", method_count(row), (float) method_count(row) / (float) total);
    }
  }
}
#endif // INCLUDE_JVMCI

void VirtualCallData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "VirtualCallData", extra);
  print_receiver_data_on(st);
  print_method_data_on(st);
}

// ==================================================================
// RetData
//
// A RetData is used to access profiling information for a ret bytecode.
// It is composed of a count of the number of times that the ret has
// been executed, followed by a series of triples of the form
// (bci, count, di) which count the number of times that some bci was the
// target of the ret and cache a corresponding displacement.

void RetData::post_initialize(BytecodeStream* stream, MethodData* mdo) {
  for (uint row = 0; row < row_limit(); row++) {
    set_bci_displacement(row, -1);
    set_bci(row, no_bci);
  }
  // release so other threads see a consistent state.  bci is used as
  // a valid flag for bci_displacement.
  OrderAccess::release();
}

// This routine needs to atomically update the RetData structure, so the
// caller needs to hold the RetData_lock before it gets here.  Since taking
// the lock can block (and allow GC) and since RetData is a ProfileData is a
// wrapper around a derived oop, taking the lock in _this_ method will
// basically cause the 'this' pointer's _data field to contain junk after the
// lock.  We require the caller to take the lock before making the ProfileData
// structure.  Currently the only caller is InterpreterRuntime::update_mdp_for_ret
address RetData::fixup_ret(int return_bci, MethodData* h_mdo) {
  // First find the mdp which corresponds to the return bci.
  address mdp = h_mdo->bci_to_dp(return_bci);

  // Now check to see if any of the cache slots are open.
  for (uint row = 0; row < row_limit(); row++) {
    if (bci(row) == no_bci) {
      set_bci_displacement(row, mdp - dp());
      set_bci_count(row, DataLayout::counter_increment);
      // Barrier to ensure displacement is written before the bci; allows
      // the interpreter to read displacement without fear of race condition.
      release_set_bci(row, return_bci);
      break;
    }
  }
  return mdp;
}

#ifdef CC_INTERP
DataLayout* RetData::advance(MethodData *md, int bci) {
  return (DataLayout*) md->bci_to_dp(bci);
}
#endif // CC_INTERP

void RetData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "RetData", extra);
  uint row;
  int entries = 0;
  for (row = 0; row < row_limit(); row++) {
    if (bci(row) != no_bci)  entries++;
  }
  st->print_cr("count(%u) entries(%u)", count(), entries);
  for (row = 0; row < row_limit(); row++) {
    if (bci(row) != no_bci) {
      tab(st);
      st->print_cr("bci(%d: count(%u) displacement(%d))",
                   bci(row), bci_count(row), bci_displacement(row));
    }
  }
}

// ==================================================================
// BranchData
//
// A BranchData is used to access profiling data for a two-way branch.
// It consists of taken and not_taken counts as well as a data displacement
// for the taken case.

void BranchData::post_initialize(BytecodeStream* stream, MethodData* mdo) {
  assert(stream->bci() == bci(), "wrong pos");
  int target = stream->dest();
  int my_di = mdo->dp_to_di(dp());
  int target_di = mdo->bci_to_di(target);
  int offset = target_di - my_di;
  set_displacement(offset);
}

void BranchData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "BranchData", extra);
  st->print_cr("taken(%u) displacement(%d)",
               taken(), displacement());
  tab(st);
  st->print_cr("not taken(%u)", not_taken());
}

// ==================================================================
// MultiBranchData
//
// A MultiBranchData is used to access profiling information for
// a multi-way branch (*switch bytecodes).  It consists of a series
// of (count, displacement) pairs, which count the number of times each
// case was taken and specify the data displacment for each branch target.

int MultiBranchData::compute_cell_count(BytecodeStream* stream) {
  int cell_count = 0;
  if (stream->code() == Bytecodes::_tableswitch) {
    Bytecode_tableswitch sw(stream->method()(), stream->bcp());
    cell_count = 1 + per_case_cell_count * (1 + sw.length()); // 1 for default
  } else {
    Bytecode_lookupswitch sw(stream->method()(), stream->bcp());
    cell_count = 1 + per_case_cell_count * (sw.number_of_pairs() + 1); // 1 for default
  }
  return cell_count;
}

void MultiBranchData::post_initialize(BytecodeStream* stream,
                                      MethodData* mdo) {
  assert(stream->bci() == bci(), "wrong pos");
  int target;
  int my_di;
  int target_di;
  int offset;
  if (stream->code() == Bytecodes::_tableswitch) {
    Bytecode_tableswitch sw(stream->method()(), stream->bcp());
    int len = sw.length();
    assert(array_len() == per_case_cell_count * (len + 1), "wrong len");
    for (int count = 0; count < len; count++) {
      target = sw.dest_offset_at(count) + bci();
      my_di = mdo->dp_to_di(dp());
      target_di = mdo->bci_to_di(target);
      offset = target_di - my_di;
      set_displacement_at(count, offset);
    }
    target = sw.default_offset() + bci();
    my_di = mdo->dp_to_di(dp());
    target_di = mdo->bci_to_di(target);
    offset = target_di - my_di;
    set_default_displacement(offset);

  } else {
    Bytecode_lookupswitch sw(stream->method()(), stream->bcp());
    int npairs = sw.number_of_pairs();
    assert(array_len() == per_case_cell_count * (npairs + 1), "wrong len");
    for (int count = 0; count < npairs; count++) {
      LookupswitchPair pair = sw.pair_at(count);
      target = pair.offset() + bci();
      my_di = mdo->dp_to_di(dp());
      target_di = mdo->bci_to_di(target);
      offset = target_di - my_di;
      set_displacement_at(count, offset);
    }
    target = sw.default_offset() + bci();
    my_di = mdo->dp_to_di(dp());
    target_di = mdo->bci_to_di(target);
    offset = target_di - my_di;
    set_default_displacement(offset);
  }
}

void MultiBranchData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "MultiBranchData", extra);
  st->print_cr("default_count(%u) displacement(%d)",
               default_count(), default_displacement());
  int cases = number_of_cases();
  for (int i = 0; i < cases; i++) {
    tab(st);
    st->print_cr("count(%u) displacement(%d)",
                 count_at(i), displacement_at(i));
  }
}

void ArgInfoData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "ArgInfoData", extra);
  int nargs = number_of_args();
  for (int i = 0; i < nargs; i++) {
    st->print("  0x%x", arg_modified(i));
  }
  st->cr();
}

int ParametersTypeData::compute_cell_count(Method* m) {
  if (!MethodData::profile_parameters_for_method(m)) {
    return 0;
  }
  int max = TypeProfileParmsLimit == -1 ? INT_MAX : TypeProfileParmsLimit;
  int obj_args = TypeStackSlotEntries::compute_cell_count(m->signature(), !m->is_static(), max);
  if (obj_args > 0) {
    return obj_args + 1; // 1 cell for array len
  }
  return 0;
}

void ParametersTypeData::post_initialize(BytecodeStream* stream, MethodData* mdo) {
  _parameters.post_initialize(mdo->method()->signature(), !mdo->method()->is_static(), true);
}

bool ParametersTypeData::profiling_enabled() {
  return MethodData::profile_parameters();
}

void ParametersTypeData::print_data_on(outputStream* st, const char* extra) const {
  st->print("parameter types"); // FIXME extra ignored?
  _parameters.print_data_on(st);
}

void SpeculativeTrapData::print_data_on(outputStream* st, const char* extra) const {
  print_shared(st, "SpeculativeTrapData", extra);
  tab(st);
  method()->print_short_name(st);
  st->cr();
}

// ==================================================================
// MethodData*
//
// A MethodData* holds information which has been collected about
// a method.

MethodData* MethodData::allocate(ClassLoaderData* loader_data, const methodHandle& method, TRAPS) {
  int size = MethodData::compute_allocation_size_in_words(method);

  return new (loader_data, size, false, MetaspaceObj::MethodDataType, THREAD)
    MethodData(method(), size, THREAD);
}

int MethodData::bytecode_cell_count(Bytecodes::Code code) {
  if (is_client_compilation_mode_vm()) {
    return no_profile_data;
  }
  switch (code) {
  case Bytecodes::_checkcast:
  case Bytecodes::_instanceof:
  case Bytecodes::_aastore:
    if (TypeProfileCasts) {
      return ReceiverTypeData::static_cell_count();
    } else {
      return BitData::static_cell_count();
    }
  case Bytecodes::_invokespecial:
  case Bytecodes::_invokestatic:
    if (MethodData::profile_arguments() || MethodData::profile_return()) {
      return variable_cell_count;
    } else {
      return CounterData::static_cell_count();
    }
  case Bytecodes::_goto:
  case Bytecodes::_goto_w:
  case Bytecodes::_jsr:
  case Bytecodes::_jsr_w:
    return JumpData::static_cell_count();
  case Bytecodes::_invokevirtual:
  case Bytecodes::_invokeinterface:
    if (MethodData::profile_arguments() || MethodData::profile_return()) {
      return variable_cell_count;
    } else {
      return VirtualCallData::static_cell_count();
    }
  case Bytecodes::_invokedynamic:
    if (MethodData::profile_arguments() || MethodData::profile_return()) {
      return variable_cell_count;
    } else {
      return CounterData::static_cell_count();
    }
  case Bytecodes::_ret:
    return RetData::static_cell_count();
  case Bytecodes::_ifeq:
  case Bytecodes::_ifne:
  case Bytecodes::_iflt:
  case Bytecodes::_ifge:
  case Bytecodes::_ifgt:
  case Bytecodes::_ifle:
  case Bytecodes::_if_icmpeq:
  case Bytecodes::_if_icmpne:
  case Bytecodes::_if_icmplt:
  case Bytecodes::_if_icmpge:
  case Bytecodes::_if_icmpgt:
  case Bytecodes::_if_icmple:
  case Bytecodes::_if_acmpeq:
  case Bytecodes::_if_acmpne:
  case Bytecodes::_ifnull:
  case Bytecodes::_ifnonnull:
    return BranchData::static_cell_count();
  case Bytecodes::_lookupswitch:
  case Bytecodes::_tableswitch:
    return variable_cell_count;
  }
  return no_profile_data;
}

// Compute the size of the profiling information corresponding to
// the current bytecode.
int MethodData::compute_data_size(BytecodeStream* stream) {
  int cell_count = bytecode_cell_count(stream->code());
  if (cell_count == no_profile_data) {
    return 0;
  }
  if (cell_count == variable_cell_count) {
    switch (stream->code()) {
    case Bytecodes::_lookupswitch:
    case Bytecodes::_tableswitch:
      cell_count = MultiBranchData::compute_cell_count(stream);
      break;
    case Bytecodes::_invokespecial:
    case Bytecodes::_invokestatic:
    case Bytecodes::_invokedynamic:
      assert(MethodData::profile_arguments() || MethodData::profile_return(), "should be collecting args profile");
      if (profile_arguments_for_invoke(stream->method(), stream->bci()) ||
          profile_return_for_invoke(stream->method(), stream->bci())) {
        cell_count = CallTypeData::compute_cell_count(stream);
      } else {
        cell_count = CounterData::static_cell_count();
      }
      break;
    case Bytecodes::_invokevirtual:
    case Bytecodes::_invokeinterface: {
      assert(MethodData::profile_arguments() || MethodData::profile_return(), "should be collecting args profile");
      if (profile_arguments_for_invoke(stream->method(), stream->bci()) ||
          profile_return_for_invoke(stream->method(), stream->bci())) {
        cell_count = VirtualCallTypeData::compute_cell_count(stream);
      } else {
        cell_count = VirtualCallData::static_cell_count();
      }
      break;
    }
    default:
      fatal("unexpected bytecode for var length profile data");
    }
  }
  // Note:  cell_count might be zero, meaning that there is just
  //        a DataLayout header, with no extra cells.
  assert(cell_count >= 0, "sanity");
  return DataLayout::compute_size_in_bytes(cell_count);
}

bool MethodData::is_speculative_trap_bytecode(Bytecodes::Code code) {
  // Bytecodes for which we may use speculation
  switch (code) {
  case Bytecodes::_checkcast:
  case Bytecodes::_instanceof:
  case Bytecodes::_aastore:
  case Bytecodes::_invokevirtual:
  case Bytecodes::_invokeinterface:
  case Bytecodes::_if_acmpeq:
  case Bytecodes::_if_acmpne:
  case Bytecodes::_ifnull:
  case Bytecodes::_ifnonnull:
  case Bytecodes::_invokestatic:
#ifdef COMPILER2
    if (is_server_compilation_mode_vm()) {
      return UseTypeSpeculation;
    }
#endif
  default:
    return false;
  }
  return false;
}

int MethodData::compute_extra_data_count(int data_size, int empty_bc_count, bool needs_speculative_traps) {
#if INCLUDE_JVMCI
  if (ProfileTraps) {
    // Assume that up to 30% of the possibly trapping BCIs with no MDP will need to allocate one.
    int extra_data_count = MIN2(empty_bc_count, MAX2(4, (empty_bc_count * 30) / 100));

    // Make sure we have a minimum number of extra data slots to
    // allocate SpeculativeTrapData entries. We would want to have one
    // entry per compilation that inlines this method and for which
    // some type speculation assumption fails. So the room we need for
    // the SpeculativeTrapData entries doesn't directly depend on the
    // size of the method. Because it's hard to estimate, we reserve
    // space for an arbitrary number of entries.
    int spec_data_count = (needs_speculative_traps ? SpecTrapLimitExtraEntries : 0) *
      (SpeculativeTrapData::static_cell_count() + DataLayout::header_size_in_cells());

    return MAX2(extra_data_count, spec_data_count);
  } else {
    return 0;
  }
#else // INCLUDE_JVMCI
  if (ProfileTraps) {
    // Assume that up to 3% of BCIs with no MDP will need to allocate one.
    int extra_data_count = (uint)(empty_bc_count * 3) / 128 + 1;
    // If the method is large, let the extra BCIs grow numerous (to ~1%).
    int one_percent_of_data
      = (uint)data_size / (DataLayout::header_size_in_bytes()*128);
    if (extra_data_count < one_percent_of_data)
      extra_data_count = one_percent_of_data;
    if (extra_data_count > empty_bc_count)
      extra_data_count = empty_bc_count;  // no need for more

    // Make sure we have a minimum number of extra data slots to
    // allocate SpeculativeTrapData entries. We would want to have one
    // entry per compilation that inlines this method and for which
    // some type speculation assumption fails. So the room we need for
    // the SpeculativeTrapData entries doesn't directly depend on the
    // size of the method. Because it's hard to estimate, we reserve
    // space for an arbitrary number of entries.
    int spec_data_count = (needs_speculative_traps ? SpecTrapLimitExtraEntries : 0) *
      (SpeculativeTrapData::static_cell_count() + DataLayout::header_size_in_cells());

    return MAX2(extra_data_count, spec_data_count);
  } else {
    return 0;
  }
#endif // INCLUDE_JVMCI
}

// Compute the size of the MethodData* necessary to store
// profiling information about a given method.  Size is in bytes.
int MethodData::compute_allocation_size_in_bytes(const methodHandle& method) {
  int data_size = 0;
  BytecodeStream stream(method);
  Bytecodes::Code c;
  int empty_bc_count = 0;  // number of bytecodes lacking data
  bool needs_speculative_traps = false;
  while ((c = stream.next()) >= 0) {
    int size_in_bytes = compute_data_size(&stream);
    data_size += size_in_bytes;
    if (size_in_bytes == 0 JVMCI_ONLY(&& Bytecodes::can_trap(c)))  empty_bc_count += 1;
    needs_speculative_traps = needs_speculative_traps || is_speculative_trap_bytecode(c);
  }
  int object_size = in_bytes(data_offset()) + data_size;

  // Add some extra DataLayout cells (at least one) to track stray traps.
  int extra_data_count = compute_extra_data_count(data_size, empty_bc_count, needs_speculative_traps);
  object_size += extra_data_count * DataLayout::compute_size_in_bytes(0);

  // Add a cell to record information about modified arguments.
  int arg_size = method->size_of_parameters();
  object_size += DataLayout::compute_size_in_bytes(arg_size+1);

  // Reserve room for an area of the MDO dedicated to profiling of
  // parameters
  int args_cell = ParametersTypeData::compute_cell_count(method());
  if (args_cell > 0) {
    object_size += DataLayout::compute_size_in_bytes(args_cell);
  }
  return object_size;
}

// Compute the size of the MethodData* necessary to store
// profiling information about a given method.  Size is in words
int MethodData::compute_allocation_size_in_words(const methodHandle& method) {
  int byte_size = compute_allocation_size_in_bytes(method);
  int word_size = align_size_up(byte_size, BytesPerWord) / BytesPerWord;
  return align_metadata_size(word_size);
}

// Initialize an individual data segment.  Returns the size of
// the segment in bytes.
int MethodData::initialize_data(BytecodeStream* stream,
                                       int data_index) {
  if (is_client_compilation_mode_vm()) {
    return 0;
  }
  int cell_count = -1;
  int tag = DataLayout::no_tag;
  DataLayout* data_layout = data_layout_at(data_index);
  Bytecodes::Code c = stream->code();
  switch (c) {
  case Bytecodes::_checkcast:
  case Bytecodes::_instanceof:
  case Bytecodes::_aastore:
    if (TypeProfileCasts) {
      cell_count = ReceiverTypeData::static_cell_count();
      tag = DataLayout::receiver_type_data_tag;
    } else {
      cell_count = BitData::static_cell_count();
      tag = DataLayout::bit_data_tag;
    }
    break;
  case Bytecodes::_invokespecial:
  case Bytecodes::_invokestatic: {
    int counter_data_cell_count = CounterData::static_cell_count();
    if (profile_arguments_for_invoke(stream->method(), stream->bci()) ||
        profile_return_for_invoke(stream->method(), stream->bci())) {
      cell_count = CallTypeData::compute_cell_count(stream);
    } else {
      cell_count = counter_data_cell_count;
    }
    if (cell_count > counter_data_cell_count) {
      tag = DataLayout::call_type_data_tag;
    } else {
      tag = DataLayout::counter_data_tag;
    }
    break;
  }
  case Bytecodes::_goto:
  case Bytecodes::_goto_w:
  case Bytecodes::_jsr:
  case Bytecodes::_jsr_w:
    cell_count = JumpData::static_cell_count();
    tag = DataLayout::jump_data_tag;
    break;
  case Bytecodes::_invokevirtual:
  case Bytecodes::_invokeinterface: {
    int virtual_call_data_cell_count = VirtualCallData::static_cell_count();
    if (profile_arguments_for_invoke(stream->method(), stream->bci()) ||
        profile_return_for_invoke(stream->method(), stream->bci())) {
      cell_count = VirtualCallTypeData::compute_cell_count(stream);
    } else {
      cell_count = virtual_call_data_cell_count;
    }
    if (cell_count > virtual_call_data_cell_count) {
      tag = DataLayout::virtual_call_type_data_tag;
    } else {
      tag = DataLayout::virtual_call_data_tag;
    }
    break;
  }
  case Bytecodes::_invokedynamic: {
    // %%% should make a type profile for any invokedynamic that takes a ref argument
    int counter_data_cell_count = CounterData::static_cell_count();
    if (profile_arguments_for_invoke(stream->method(), stream->bci()) ||
        profile_return_for_invoke(stream->method(), stream->bci())) {
      cell_count = CallTypeData::compute_cell_count(stream);
    } else {
      cell_count = counter_data_cell_count;
    }
    if (cell_count > counter_data_cell_count) {
      tag = DataLayout::call_type_data_tag;
    } else {
      tag = DataLayout::counter_data_tag;
    }
    break;
  }
  case Bytecodes::_ret:
    cell_count = RetData::static_cell_count();
    tag = DataLayout::ret_data_tag;
    break;
  case Bytecodes::_ifeq:
  case Bytecodes::_ifne:
  case Bytecodes::_iflt:
  case Bytecodes::_ifge:
  case Bytecodes::_ifgt:
  case Bytecodes::_ifle:
  case Bytecodes::_if_icmpeq:
  case Bytecodes::_if_icmpne:
  case Bytecodes::_if_icmplt:
  case Bytecodes::_if_icmpge:
  case Bytecodes::_if_icmpgt:
  case Bytecodes::_if_icmple:
  case Bytecodes::_if_acmpeq:
  case Bytecodes::_if_acmpne:
  case Bytecodes::_ifnull:
  case Bytecodes::_ifnonnull:
    cell_count = BranchData::static_cell_count();
    tag = DataLayout::branch_data_tag;
    break;
  case Bytecodes::_lookupswitch:
  case Bytecodes::_tableswitch:
    cell_count = MultiBranchData::compute_cell_count(stream);
    tag = DataLayout::multi_branch_data_tag;
    break;
  }
  assert(tag == DataLayout::multi_branch_data_tag ||
         ((MethodData::profile_arguments() || MethodData::profile_return()) &&
          (tag == DataLayout::call_type_data_tag ||
           tag == DataLayout::counter_data_tag ||
           tag == DataLayout::virtual_call_type_data_tag ||
           tag == DataLayout::virtual_call_data_tag)) ||
         cell_count == bytecode_cell_count(c), "cell counts must agree");
  if (cell_count >= 0) {
    assert(tag != DataLayout::no_tag, "bad tag");
    assert(bytecode_has_profile(c), "agree w/ BHP");
    data_layout->initialize(tag, stream->bci(), cell_count);
    return DataLayout::compute_size_in_bytes(cell_count);
  } else {
    assert(!bytecode_has_profile(c), "agree w/ !BHP");
    return 0;
  }
}

// Get the data at an arbitrary (sort of) data index.
ProfileData* MethodData::data_at(int data_index) const {
  if (out_of_bounds(data_index)) {
    return NULL;
  }
  DataLayout* data_layout = data_layout_at(data_index);
  return data_layout->data_in();
}

ProfileData* DataLayout::data_in() {
  switch (tag()) {
  case DataLayout::no_tag:
  default:
    ShouldNotReachHere();
    return NULL;
  case DataLayout::bit_data_tag:
    return new BitData(this);
  case DataLayout::counter_data_tag:
    return new CounterData(this);
  case DataLayout::jump_data_tag:
    return new JumpData(this);
  case DataLayout::receiver_type_data_tag:
    return new ReceiverTypeData(this);
  case DataLayout::virtual_call_data_tag:
    return new VirtualCallData(this);
  case DataLayout::ret_data_tag:
    return new RetData(this);
  case DataLayout::branch_data_tag:
    return new BranchData(this);
  case DataLayout::multi_branch_data_tag:
    return new MultiBranchData(this);
  case DataLayout::arg_info_data_tag:
    return new ArgInfoData(this);
  case DataLayout::call_type_data_tag:
    return new CallTypeData(this);
  case DataLayout::virtual_call_type_data_tag:
    return new VirtualCallTypeData(this);
  case DataLayout::parameters_type_data_tag:
    return new ParametersTypeData(this);
  case DataLayout::speculative_trap_data_tag:
    return new SpeculativeTrapData(this);
  }
}

// Iteration over data.
ProfileData* MethodData::next_data(ProfileData* current) const {
  int current_index = dp_to_di(current->dp());
  int next_index = current_index + current->size_in_bytes();
  ProfileData* next = data_at(next_index);
  return next;
}

// Give each of the data entries a chance to perform specific
// data initialization.
void MethodData::post_initialize(BytecodeStream* stream) {
  ResourceMark rm;
  ProfileData* data;
  for (data = first_data(); is_valid(data); data = next_data(data)) {
    stream->set_start(data->bci());
    stream->next();
    data->post_initialize(stream, this);
  }
  if (_parameters_type_data_di != no_parameters) {
    parameters_type_data()->post_initialize(NULL, this);
  }
}

// Initialize the MethodData* corresponding to a given method.
MethodData::MethodData(const methodHandle& method, int size, TRAPS)
  : _extra_data_lock(Monitor::leaf, "MDO extra data lock"),
    _parameters_type_data_di(parameters_uninitialized) {
  // Set the method back-pointer.
  _method = method();
  initialize();
}

void MethodData::initialize() {
  NoSafepointVerifier no_safepoint;  // init function atomic wrt GC
  ResourceMark rm;

  init();
  set_creation_mileage(mileage_of(method()));

  // Go through the bytecodes and allocate and initialize the
  // corresponding data cells.
  int data_size = 0;
  int empty_bc_count = 0;  // number of bytecodes lacking data
  _data[0] = 0;  // apparently not set below.
  BytecodeStream stream(method());
  Bytecodes::Code c;
  bool needs_speculative_traps = false;
  while ((c = stream.next()) >= 0) {
    int size_in_bytes = initialize_data(&stream, data_size);
    data_size += size_in_bytes;
    if (size_in_bytes == 0 JVMCI_ONLY(&& Bytecodes::can_trap(c)))  empty_bc_count += 1;
    needs_speculative_traps = needs_speculative_traps || is_speculative_trap_bytecode(c);
  }
  _data_size = data_size;
  int object_size = in_bytes(data_offset()) + data_size;

  // Add some extra DataLayout cells (at least one) to track stray traps.
  int extra_data_count = compute_extra_data_count(data_size, empty_bc_count, needs_speculative_traps);
  int extra_size = extra_data_count * DataLayout::compute_size_in_bytes(0);

  // Let's zero the space for the extra data
  Copy::zero_to_bytes(((address)_data) + data_size, extra_size);

  // Add a cell to record information about modified arguments.
  // Set up _args_modified array after traps cells so that
  // the code for traps cells works.
  DataLayout *dp = data_layout_at(data_size + extra_size);

  int arg_size = method()->size_of_parameters();
  dp->initialize(DataLayout::arg_info_data_tag, 0, arg_size+1);

  int arg_data_size = DataLayout::compute_size_in_bytes(arg_size+1);
  object_size += extra_size + arg_data_size;

  int parms_cell = ParametersTypeData::compute_cell_count(method());
  // If we are profiling parameters, we reserver an area near the end
  // of the MDO after the slots for bytecodes (because there's no bci
  // for method entry so they don't fit with the framework for the
  // profiling of bytecodes). We store the offset within the MDO of
  // this area (or -1 if no parameter is profiled)
  if (parms_cell > 0) {
    object_size += DataLayout::compute_size_in_bytes(parms_cell);
    _parameters_type_data_di = data_size + extra_size + arg_data_size;
    DataLayout *dp = data_layout_at(data_size + extra_size + arg_data_size);
    dp->initialize(DataLayout::parameters_type_data_tag, 0, parms_cell);
  } else {
    _parameters_type_data_di = no_parameters;
  }

  // Set an initial hint. Don't use set_hint_di() because
  // first_di() may be out of bounds if data_size is 0.
  // In that situation, _hint_di is never used, but at
  // least well-defined.
  _hint_di = first_di();

  post_initialize(&stream);

  assert(object_size == compute_allocation_size_in_bytes(methodHandle(_method)), "MethodData: computed size != initialized size");
  set_size(object_size);

  if(LoadProfilingDataOnInvocation) {
    const rapidjson::Value *obj = this->method()->try_lookup_prof_data();
    if(obj) {
      // We need to allow safepoints to occur here since a lock is taken when
      // deserializing class names.
      PauseNoSafepointVerifier pause(&no_safepoint);
      this->deserialize_from_json((*obj)["mdo"]);
    }
  }
}

void MethodData::init() {
  _invocation_counter.init();
  _backedge_counter.init();
  _invocation_counter_start = 0;
  _backedge_counter_start = 0;

  // Set per-method invoke- and backedge mask.
  double scale = 1.0;
  CompilerOracle::has_option_value(_method, "CompileThresholdScaling", scale);
  _invoke_mask = right_n_bits(Arguments::scaled_freq_log(Tier0InvokeNotifyFreqLog, scale)) << InvocationCounter::count_shift;
  _backedge_mask = right_n_bits(Arguments::scaled_freq_log(Tier0BackedgeNotifyFreqLog, scale)) << InvocationCounter::count_shift;

  _tenure_traps = 0;
  _num_loops = 0;
  _num_blocks = 0;
  _would_profile = unknown;

#if INCLUDE_JVMCI
  _jvmci_ir_size = 0;
#endif

#if INCLUDE_RTM_OPT
  _rtm_state = NoRTM; // No RTM lock eliding by default
  if (UseRTMLocking &&
      !CompilerOracle::has_option_string(_method, "NoRTMLockEliding")) {
    if (CompilerOracle::has_option_string(_method, "UseRTMLockEliding") || !UseRTMDeopt) {
      // Generate RTM lock eliding code without abort ratio calculation code.
      _rtm_state = UseRTM;
    } else if (UseRTMDeopt) {
      // Generate RTM lock eliding code and include abort ratio calculation
      // code if UseRTMDeopt is on.
      _rtm_state = ProfileRTM;
    }
  }
#endif

  // Initialize flags and trap history.
  _nof_decompiles = 0;
  _nof_overflow_recompiles = 0;
  _nof_overflow_traps = 0;
  clear_escape_info();
  assert(sizeof(_trap_hist) % sizeof(HeapWord) == 0, "align");
  Copy::zero_to_words((HeapWord*) &_trap_hist,
                      sizeof(_trap_hist) / sizeof(HeapWord));
}

// Get a measure of how much mileage the method has on it.
int MethodData::mileage_of(Method* method) {
  int mileage = 0;
  if (TieredCompilation) {
    mileage = MAX2(method->invocation_count(), method->backedge_count());
  } else {
    int iic = method->interpreter_invocation_count();
    if (mileage < iic)  mileage = iic;
    MethodCounters* mcs = method->method_counters();
    if (mcs != NULL) {
      InvocationCounter* ic = mcs->invocation_counter();
      InvocationCounter* bc = mcs->backedge_counter();
      int icval = ic->count();
      if (ic->carry()) icval += CompileThreshold;
      if (mileage < icval)  mileage = icval;
      int bcval = bc->count();
      if (bc->carry()) bcval += CompileThreshold;
      if (mileage < bcval)  mileage = bcval;
    }
  }
  return mileage;
}

bool MethodData::is_mature() const {
  if(IgnoreMethodMaturity) {
    return true;
  }
  return CompilationPolicy::policy()->is_mature(_method);
}

// Translate a bci to its corresponding data index (di).
address MethodData::bci_to_dp(int bci) {
  ResourceMark rm;
  ProfileData* data = data_before(bci);
  ProfileData* prev = NULL;
  for ( ; is_valid(data); data = next_data(data)) {
    if (data->bci() >= bci) {
      if (data->bci() == bci)  set_hint_di(dp_to_di(data->dp()));
      else if (prev != NULL)   set_hint_di(dp_to_di(prev->dp()));
      return data->dp();
    }
    prev = data;
  }
  return (address)limit_data_position();
}

// Translate a bci to its corresponding data, or NULL.
ProfileData* MethodData::bci_to_data(int bci) {
  ProfileData* data = data_before(bci);
  for ( ; is_valid(data); data = next_data(data)) {
    if (data->bci() == bci) {
      set_hint_di(dp_to_di(data->dp()));
      return data;
    } else if (data->bci() > bci) {
      break;
    }
  }
  return bci_to_extra_data(bci, NULL, false);
}

DataLayout* MethodData::next_extra(DataLayout* dp) {
  int nb_cells = 0;
  switch(dp->tag()) {
  case DataLayout::bit_data_tag:
  case DataLayout::no_tag:
    nb_cells = BitData::static_cell_count();
    break;
  case DataLayout::speculative_trap_data_tag:
    nb_cells = SpeculativeTrapData::static_cell_count();
    break;
  default:
    fatal("unexpected tag %d", dp->tag());
  }
  return (DataLayout*)((address)dp + DataLayout::compute_size_in_bytes(nb_cells));
}

ProfileData* MethodData::bci_to_extra_data_helper(int bci, Method* m, DataLayout*& dp, bool concurrent) {
  DataLayout* end = args_data_limit();

  for (;; dp = next_extra(dp)) {
    assert(dp < end, "moved past end of extra data");
    // No need for "OrderAccess::load_acquire" ops,
    // since the data structure is monotonic.
    switch(dp->tag()) {
    case DataLayout::no_tag:
      return NULL;
    case DataLayout::arg_info_data_tag:
      dp = end;
      return NULL; // ArgInfoData is at the end of extra data section.
    case DataLayout::bit_data_tag:
      if (m == NULL && dp->bci() == bci) {
        return new BitData(dp);
      }
      break;
    case DataLayout::speculative_trap_data_tag:
      if (m != NULL) {
        SpeculativeTrapData* data = new SpeculativeTrapData(dp);
        // data->method() may be null in case of a concurrent
        // allocation. Maybe it's for the same method. Try to use that
        // entry in that case.
        if (dp->bci() == bci) {
          if (data->method() == NULL) {
            assert(concurrent, "impossible because no concurrent allocation");
            return NULL;
          } else if (data->method() == m) {
            return data;
          }
        }
      }
      break;
    default:
      fatal("unexpected tag %d", dp->tag());
    }
  }
  return NULL;
}


// Translate a bci to its corresponding extra data, or NULL.
ProfileData* MethodData::bci_to_extra_data(int bci, Method* m, bool create_if_missing) {
  // This code assumes an entry for a SpeculativeTrapData is 2 cells
  assert(2*DataLayout::compute_size_in_bytes(BitData::static_cell_count()) ==
         DataLayout::compute_size_in_bytes(SpeculativeTrapData::static_cell_count()),
         "code needs to be adjusted");

  // Do not create one of these if method has been redefined.
  if (m != NULL && m->is_old()) {
    return NULL;
  }

  DataLayout* dp  = extra_data_base();
  DataLayout* end = args_data_limit();

  // Allocation in the extra data space has to be atomic because not
  // all entries have the same size and non atomic concurrent
  // allocation would result in a corrupted extra data space.
  ProfileData* result = bci_to_extra_data_helper(bci, m, dp, true);
  if (result != NULL) {
    return result;
  }

  if (create_if_missing && dp < end) {
    MutexLocker ml(&_extra_data_lock);
    // Check again now that we have the lock. Another thread may
    // have added extra data entries.
    ProfileData* result = bci_to_extra_data_helper(bci, m, dp, false);
    if (result != NULL || dp >= end) {
      return result;
    }

    assert(dp->tag() == DataLayout::no_tag || (dp->tag() == DataLayout::speculative_trap_data_tag && m != NULL), "should be free");
    assert(next_extra(dp)->tag() == DataLayout::no_tag || next_extra(dp)->tag() == DataLayout::arg_info_data_tag, "should be free or arg info");
    u1 tag = m == NULL ? DataLayout::bit_data_tag : DataLayout::speculative_trap_data_tag;
    // SpeculativeTrapData is 2 slots. Make sure we have room.
    if (m != NULL && next_extra(dp)->tag() != DataLayout::no_tag) {
      return NULL;
    }
    DataLayout temp;
    temp.initialize(tag, bci, 0);

    dp->set_header(temp.header());
    assert(dp->tag() == tag, "sane");
    assert(dp->bci() == bci, "no concurrent allocation");
    if (tag == DataLayout::bit_data_tag) {
      return new BitData(dp);
    } else {
      SpeculativeTrapData* data = new SpeculativeTrapData(dp);
      data->set_method(m);
      return data;
    }
  }
  return NULL;
}

ArgInfoData *MethodData::arg_info() {
  DataLayout* dp    = extra_data_base();
  DataLayout* end   = args_data_limit();
  for (; dp < end; dp = next_extra(dp)) {
    if (dp->tag() == DataLayout::arg_info_data_tag)
      return new ArgInfoData(dp);
  }
  return NULL;
}

// Printing

void MethodData::print_on(outputStream* st) const {
  assert(is_methodData(), "should be method data");
  st->print("method data for ");
  method()->print_value_on(st);
  st->cr();
  print_data_on(st);
}

void MethodData::print_value_on(outputStream* st) const {
  assert(is_methodData(), "should be method data");
  st->print("method data for ");
  method()->print_value_on(st);
}

void MethodData::print_data_on(outputStream* st) const {
  ResourceMark rm;
  ProfileData* data = first_data();
  if (_parameters_type_data_di != no_parameters) {
    parameters_type_data()->print_data_on(st);
  }
  for ( ; is_valid(data); data = next_data(data)) {
    st->print("%d", dp_to_di(data->dp()));
    st->fill_to(6);
    data->print_data_on(st, this);
  }
  st->print_cr("--- Extra data:");
  DataLayout* dp    = extra_data_base();
  DataLayout* end   = args_data_limit();
  for (;; dp = next_extra(dp)) {
    assert(dp < end, "moved past end of extra data");
    // No need for "OrderAccess::load_acquire" ops,
    // since the data structure is monotonic.
    switch(dp->tag()) {
    case DataLayout::no_tag:
      continue;
    case DataLayout::bit_data_tag:
      data = new BitData(dp);
      break;
    case DataLayout::speculative_trap_data_tag:
      data = new SpeculativeTrapData(dp);
      break;
    case DataLayout::arg_info_data_tag:
      data = new ArgInfoData(dp);
      dp = end; // ArgInfoData is at the end of extra data section.
      break;
    default:
      fatal("unexpected tag %d", dp->tag());
    }
    st->print("%d", dp_to_di(data->dp()));
    st->fill_to(6);
    data->print_data_on(st);
    if (dp >= end) return;
  }
}

#if INCLUDE_SERVICES
// Size Statistics
void MethodData::collect_statistics(KlassSizeStats *sz) const {
  int n = sz->count(this);
  sz->_method_data_bytes += n;
  sz->_method_all_bytes += n;
  sz->_rw_bytes += n;
}
#endif // INCLUDE_SERVICES

// Verification

void MethodData::verify_on(outputStream* st) {
  guarantee(is_methodData(), "object must be method data");
  // guarantee(m->is_perm(), "should be in permspace");
  this->verify_data_on(st);
}

void MethodData::verify_data_on(outputStream* st) {
  NEEDS_CLEANUP;
  // not yet implemented.
}

bool MethodData::profile_jsr292(const methodHandle& m, int bci) {
  if (m->is_compiled_lambda_form()) {
    return true;
  }

  Bytecode_invoke inv(m , bci);
  return inv.is_invokedynamic() || inv.is_invokehandle();
}

int MethodData::profile_arguments_flag() {
  return TypeProfileLevel % 10;
}

bool MethodData::profile_arguments() {
  return profile_arguments_flag() > no_type_profile && profile_arguments_flag() <= type_profile_all;
}

bool MethodData::profile_arguments_jsr292_only() {
  return profile_arguments_flag() == type_profile_jsr292;
}

bool MethodData::profile_all_arguments() {
  return profile_arguments_flag() == type_profile_all;
}

bool MethodData::profile_arguments_for_invoke(const methodHandle& m, int bci) {
  if (!profile_arguments()) {
    return false;
  }

  if (profile_all_arguments()) {
    return true;
  }

  assert(profile_arguments_jsr292_only(), "inconsistent");
  return profile_jsr292(m, bci);
}

int MethodData::profile_return_flag() {
  return (TypeProfileLevel % 100) / 10;
}

bool MethodData::profile_return() {
  return profile_return_flag() > no_type_profile && profile_return_flag() <= type_profile_all;
}

bool MethodData::profile_return_jsr292_only() {
  return profile_return_flag() == type_profile_jsr292;
}

bool MethodData::profile_all_return() {
  return profile_return_flag() == type_profile_all;
}

bool MethodData::profile_return_for_invoke(const methodHandle& m, int bci) {
  if (!profile_return()) {
    return false;
  }

  if (profile_all_return()) {
    return true;
  }

  assert(profile_return_jsr292_only(), "inconsistent");
  return profile_jsr292(m, bci);
}

int MethodData::profile_parameters_flag() {
  return TypeProfileLevel / 100;
}

bool MethodData::profile_parameters() {
  return profile_parameters_flag() > no_type_profile && profile_parameters_flag() <= type_profile_all;
}

bool MethodData::profile_parameters_jsr292_only() {
  return profile_parameters_flag() == type_profile_jsr292;
}

bool MethodData::profile_all_parameters() {
  return profile_parameters_flag() == type_profile_all;
}

bool MethodData::profile_parameters_for_method(const methodHandle& m) {
  if (!profile_parameters()) {
    return false;
  }

  if (profile_all_parameters()) {
    return true;
  }

  assert(profile_parameters_jsr292_only(), "inconsistent");
  return m->is_compiled_lambda_form();
}

void MethodData::clean_extra_data_helper(DataLayout* dp, int shift, bool reset) {
  if (shift == 0) {
    return;
  }
  if (!reset) {
    // Move all cells of trap entry at dp left by "shift" cells
    intptr_t* start = (intptr_t*)dp;
    intptr_t* end = (intptr_t*)next_extra(dp);
    for (intptr_t* ptr = start; ptr < end; ptr++) {
      *(ptr-shift) = *ptr;
    }
  } else {
    // Reset "shift" cells stopping at dp
    intptr_t* start = ((intptr_t*)dp) - shift;
    intptr_t* end = (intptr_t*)dp;
    for (intptr_t* ptr = start; ptr < end; ptr++) {
      *ptr = 0;
    }
  }
}

class CleanExtraDataClosure : public StackObj {
public:
  virtual bool is_live(Method* m) = 0;
};

// Check for entries that reference an unloaded method
class CleanExtraDataKlassClosure : public CleanExtraDataClosure {
private:
  BoolObjectClosure* _is_alive;
public:
  CleanExtraDataKlassClosure(BoolObjectClosure* is_alive) : _is_alive(is_alive) {}
  bool is_live(Method* m) {
    return m->method_holder()->is_loader_alive(_is_alive);
  }
};

// Check for entries that reference a redefined method
class CleanExtraDataMethodClosure : public CleanExtraDataClosure {
public:
  CleanExtraDataMethodClosure() {}
  bool is_live(Method* m) { return !m->is_old(); }
};


// Remove SpeculativeTrapData entries that reference an unloaded or
// redefined method
void MethodData::clean_extra_data(CleanExtraDataClosure* cl) {
  DataLayout* dp  = extra_data_base();
  DataLayout* end = args_data_limit();

  int shift = 0;
  for (; dp < end; dp = next_extra(dp)) {
    switch(dp->tag()) {
    case DataLayout::speculative_trap_data_tag: {
      SpeculativeTrapData* data = new SpeculativeTrapData(dp);
      Method* m = data->method();
      assert(m != NULL, "should have a method");
      if (!cl->is_live(m)) {
        // "shift" accumulates the number of cells for dead
        // SpeculativeTrapData entries that have been seen so
        // far. Following entries must be shifted left by that many
        // cells to remove the dead SpeculativeTrapData entries.
        shift += (int)((intptr_t*)next_extra(dp) - (intptr_t*)dp);
      } else {
        // Shift this entry left if it follows dead
        // SpeculativeTrapData entries
        clean_extra_data_helper(dp, shift);
      }
      break;
    }
    case DataLayout::bit_data_tag:
      // Shift this entry left if it follows dead SpeculativeTrapData
      // entries
      clean_extra_data_helper(dp, shift);
      continue;
    case DataLayout::no_tag:
    case DataLayout::arg_info_data_tag:
      // We are at end of the live trap entries. The previous "shift"
      // cells contain entries that are either dead or were shifted
      // left. They need to be reset to no_tag
      clean_extra_data_helper(dp, shift, true);
      return;
    default:
      fatal("unexpected tag %d", dp->tag());
    }
  }
}

// Verify there's no unloaded or redefined method referenced by a
// SpeculativeTrapData entry
void MethodData::verify_extra_data_clean(CleanExtraDataClosure* cl) {
#ifdef ASSERT
  DataLayout* dp  = extra_data_base();
  DataLayout* end = args_data_limit();

  for (; dp < end; dp = next_extra(dp)) {
    switch(dp->tag()) {
    case DataLayout::speculative_trap_data_tag: {
      SpeculativeTrapData* data = new SpeculativeTrapData(dp);
      Method* m = data->method();
      assert(m != NULL && cl->is_live(m), "Method should exist");
      break;
    }
    case DataLayout::bit_data_tag:
      continue;
    case DataLayout::no_tag:
    case DataLayout::arg_info_data_tag:
      return;
    default:
      fatal("unexpected tag %d", dp->tag());
    }
  }
#endif
}

void MethodData::clean_method_data(BoolObjectClosure* is_alive) {
  ResourceMark rm;
  for (ProfileData* data = first_data();
       is_valid(data);
       data = next_data(data)) {
    data->clean_weak_klass_links(is_alive);
  }
  ParametersTypeData* parameters = parameters_type_data();
  if (parameters != NULL) {
    parameters->clean_weak_klass_links(is_alive);
  }

  CleanExtraDataKlassClosure cl(is_alive);
  clean_extra_data(&cl);
  verify_extra_data_clean(&cl);
}

void MethodData::clean_weak_method_links() {
  ResourceMark rm;
  for (ProfileData* data = first_data();
       is_valid(data);
       data = next_data(data)) {
    data->clean_weak_method_links();
  }

  CleanExtraDataMethodClosure cl;
  clean_extra_data(&cl);
  verify_extra_data_clean(&cl);
}

#ifdef ASSERT
void MethodData::verify_clean_weak_method_links() {
  ResourceMark rm;
  for (ProfileData* data = first_data();
       is_valid(data);
       data = next_data(data)) {
    data->verify_clean_weak_method_links();
  }

  CleanExtraDataMethodClosure cl;
  verify_extra_data_clean(&cl);
}
#endif // ASSERT

// Serialization methods

DECL_JSON_FIELD_SPEC(MethodData::WouldProfile, fprintf(f, "%u", data);,
                                          data = (MethodData::WouldProfile)json.GetUint();)
DECL_JSON_FIELD_SPEC(InvocationCounter, fprintf(f, "%u", data.raw_counter());,
                                   data.set_raw_counter(json.GetUint());)

// (De)serializing trap_hist is a little complicated, so we need some helper
// functions.
void serialize_byte_array(FILE *f, void *data, size_t len) {
  const unsigned char *cdata = (const unsigned char*)data;
  fputc('"', f);
  for(unsigned i = 0; i < len; i++) {
    fprintf(f, "%02X", cdata[i]);
  }
  fputc('"', f);
}

void deserialize_byte_array(const rapidjson::Value &json, void *data, size_t len) {
  assert(json.IsString() && json.GetStringLength() / 2 == len, "invalid json");

  char *cdata = (char*)data;
  const char *json_str = json.GetString();
  for(unsigned i = 0; i < len; i++) {
    char upper = json_str[i * 2];
    char lower = json_str[i * 2 + 1];

    cdata[i] = 0;
    if(isdigit(upper))
      cdata[i] += (upper - '0') << 8;
    else
      cdata[i] += (upper - 'A' + 10) << 8;

    if(isdigit(lower))
      cdata[i] += (lower - '0');
    else
      cdata[i] += (lower - 'A' + 10);

  }
}

DECL_JSON_FIELD_SPEC(MethodData::trap_hist,
    serialize_byte_array(f, data._array, MethodData::_trap_hist_limit);,
    deserialize_byte_array(json, data._array, MethodData::_trap_hist_limit);)


Serializer<MethodData> MethodData::serializer() {
  static const FieldSerializer<MethodData> fields[] = {
#define FIELD(NAME) \
    FieldSerializer<MethodData>::build(#NAME, &MethodData::NAME),
    FIELD(_nof_decompiles)
    FIELD(_nof_overflow_recompiles)
    FIELD(_nof_overflow_traps)
    FIELD(_trap_hist)
    FIELD(_eflags)
    FIELD(_arg_local)
    FIELD(_arg_stack)
    FIELD(_arg_returned)
    FIELD(_creation_mileage)
    FIELD(_invocation_counter)
    FIELD(_backedge_counter)
    FIELD(_invocation_counter_start)
    FIELD(_backedge_counter_start)
    FIELD(_tenure_traps)
    //FIELD(_invoke_mask)
    //FIELD(_backedge_mask)
#if INCLUDE_RTM_OPT
    FIELD(_rtm_state)
#endif
    FIELD(_num_loops)
    FIELD(_num_blocks)
    FIELD(_would_profile)
    FIELD(_data_size)
    FIELD(_parameters_type_data_di)
    FIELD(_size)
  };
  Serializer<MethodData> sr(fields);
  if(SkipSerializedInvokeAndBackedgeCounters) {
    static const FieldSerializer<MethodData> skipped_counter_fields[] = {
      FIELD(_invocation_counter)
      FIELD(_backedge_counter)
      FIELD(_invocation_counter_start)
      FIELD(_backedge_counter_start)
    };
    sr.skip_fields(skipped_counter_fields);
  }
#undef FIELD
  return sr;
}


// The following two functions should be method on TypeStackSlotEntries and
// ReturnTypeEntry, but can't because the functions should output something
// if the object itself is absent, which isn't possible with a methid.
template<typename T>
void serialize_tsse(const T *t, const Indenter& indent, FILE *f) {

  fprintf(f, "[\n");
  if(t->has_arguments()) {
    for(int i = 0; i < t->args()->number_of_entries(); i++) {
      Klass *kls = TypeEntries::valid_klass(t->args()->type(i));
      uint flags = t->args()->type(i) & 3;
      const char *kls_name = (kls == NULL) ? "" : kls->name()->as_C_string();

      fprintf(f, "%s\n%s{\n"
                     "%s\"type\": \"%s\",\n"
                     "%s\"flags\": %u,\n"
                     "%s\"slot\": %u\n"
                    "%s}", (i == 0) ? "" : ",", indent(2),
                           indent(4), kls_name,
                           indent(4), flags,
                           indent(4), t->args()->stack_slot(i),
                           indent(2)
        );
    }
    fprintf(f, "\n%s]", indent());
  } else {
    fputs(" ]", f);
  }
}


template<typename T>
void serialize_rse(const T *t, FILE *f) {

  uint flags = 0;
  char ret_name[1024] = { };
  if(t->has_return()) {
    Klass *kls = TypeEntries::valid_klass(t->ret()->type());
    if(kls != NULL) {
        kls->name()->as_C_string(ret_name, sizeof(ret_name));
    }
    flags = t->ret()->type() & 3;
  }

  fprintf(f, "{ \"type\": \"%s\", \"flags\": %d }", ret_name, flags);
}

void MethodData::serialize_to_file(int indent_, FILE *f) const {

  const Serializer<MethodData> &sr = MethodData::serializer();

  Indenter indent(indent_);

  fprintf(f, "{\n%s\"fields\": ", indent(2));

  sr.serialize_to_file(this, indent + 2, f);
  fprintf(f, ",\n%s\"data\": [\n", indent(2));


  ProfileData* data = first_data();
  //assert(_parameters_type_data_di == no_parameters, "Uncomment the following block?");
  if (_parameters_type_data_di != no_parameters) {
    fputs(indent(4), f);
    parameters_type_data()->serialize_to_file(indent + 4, f);

    fprintf(f, "%s\n", is_valid(next_data(data)) || extra_data_base() < args_data_limit() ? "," : "");
  }

  for ( ; is_valid(data); data = next_data(data)) {
    fputs(indent(4), f);
    data->serialize_to_file(indent + 4, f);
    fprintf(f, "%s\n", is_valid(next_data(data)) ? "," : "");
  }

  fprintf(f, "%s],\n%s\"extra_data\": [\n%s", indent(2), indent(2), indent(4));
  DataLayout* dp    = extra_data_base();
  DataLayout* end   = args_data_limit();
  for(bool first = true;; dp = next_extra(dp)) {
    if(dp >= end) {
      break;
    }

    // JSON's lack of trailing commas is awful
    if(first) {
      first = false;
    } else {
      fputs(",\n", f);
      fputs(indent(4), f);
    }

    int tag = dp->tag();
    data = NULL;

    if(tag == DataLayout::no_tag) {
      fputs("{ }", f);
      continue;
    } else if(tag == DataLayout::bit_data_tag) {
      data = new BitData(dp);
    } else if(tag == DataLayout::speculative_trap_data_tag) {
      data = new SpeculativeTrapData(dp);
    } else if(tag == DataLayout::arg_info_data_tag) {
      data = new ArgInfoData(dp);
    } else {
      assert(false, "Unexpected extra data tag");
    }

    //data = dp->data_in();
    data->serialize_to_file(indent + 4, f);


    if(tag == DataLayout::arg_info_data_tag) {
      break;
    }
  }

  fprintf(f, "\n%s]\n%s}", indent(2), indent());
}

void BitData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"BitData\",\n"
             "%s\"header\": %llu,\n"
             "%s\"cell_count\": %d,\n"
             "%s\"null_seen\": %u\n"
             "%s}", indent(2), indent(2), this->data()->header(), indent(2),
                    this->cell_count(), indent(2), this->null_seen(), indent());
}

void CounterData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"CounterData\",\n"
             "%s\"header\": %llu,\n"
             "%s\"count\": %u,\n"
             "%s\"cell_count\": %d\n"
             "%s}", indent(2), indent(2), this->data()->header(), indent(2),
                    this->count(), indent(2), this->cell_count(), indent());
}

void ReceiverTypeData::serialize_to_file_shared(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"%s\",\n"
             "%s\"count\": %u,\n"
             "%s\"cell_count\": %d,\n"
             "%s\"header\": %llu,\n"
             "%s\"receivers\": [",
        indent(2), this->class_name(),
        indent(2), this->count(),
        indent(2), this->cell_count(),
        indent(2), this->data()->header(),
        indent(2)
  );

  for(uint i = 0; i < this->row_limit(); i++) {
    fprintf(f, "%s\n%s", (i != 0) ? "," : "", indent(4));

    Klass *k = this->receiver(i);
    if(k == NULL) {
      fputs("{ }", f);
    } else {

      fprintf(f, "{\n"
                 "%s\"class\": \"%s\",\n"
                 "%s\"count\": %u\n"
                 "%s}",
          indent(6), k->name()->as_C_string(),
          indent(6), this->receiver_count(i),
          indent(4)
      );
    }
  }

  fprintf(f, "\n%s]", indent(2));
}

void ReceiverTypeData::serialize_to_file(const Indenter& indent, FILE *f) const {
  this->serialize_to_file_shared(indent, f);
  fprintf(f, "\n%s}", indent());
}

void VirtualCallData::serialize_to_file(const Indenter& indent, FILE *f) const {
  this->ReceiverTypeData::serialize_to_file(indent, f);
}

void VirtualCallTypeData::serialize_to_file(const Indenter& indent, FILE *f) const {
  this->serialize_to_file_shared(indent, f);

  fprintf(f, ",\n"
             "%s\"args\": ", indent(2));
  serialize_tsse(this, indent, f);

  fprintf(f, ",\n"
             "%s\"return\": ", indent(2));
  serialize_rse(this, f);

  fprintf(f, "\n%s}", indent());
}

void RetData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"RetData\",\n"
             "%s\"header\": %llu,\n"
             "%s\"count\": %u,\n"
             "%s\"cell_count\": %d,\n"
             "%s\"items\": [",
        indent(2),
        indent(2), this->data()->header(),
        indent(2), this->count(),
        indent(2), this->cell_count(),
        indent(2)
  );

  for(uint i = 0; i < this->row_limit(); i++) {
    fprintf(f, "%s\n"
               "%s{\n"
               "%s\"bci\": %d,\n"
               "%s\"bci_count\": %u,\n"
               "%s\"bci_displacement\": %d\n"
               "%s}",
        (i != 0) ? "," : "",
        indent(4),
        indent(6), this->bci(i),
        indent(6), this->bci_count(i),
        indent(6), this->bci_displacement(i),
        indent(4)
    );
  }

  fprintf(f, "\n%s]\n%s}", indent(2), indent());
}

// XXX Only dacapo jython, luindex & tradesoap seems to produce this structure
//     Only tradesoap produces non-empty "return" values
//     None produce non-empty "args" values
void CallTypeData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"CallTypeData\",\n"
             "%s\"header\": %llu,\n"
             "%s\"count\": %u,\n"
             "%s\"cell_count\": %d,\n"
             "%s\"args\": ",
        indent(2),
        indent(2), this->data()->header(),
        indent(2), this->count(),
        indent(2), this->cell_count(),
        indent(2)
    );

  serialize_tsse(this, indent + 2, f);

  fprintf(f, ",\n"
             "%s\"return\": ", indent(2));
  serialize_rse(this, f);

  fprintf(f, "\n%s}", indent());
}

void JumpData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"%s\",\n"
             "%s\"header\": %llu,\n"
             "%s\"taken\": %u,\n"
             "%s\"displacement\": %d,\n"
             "%s\"cell_count\": %d\n"
             "%s}", indent(2), this->class_name(),
                    indent(2), this->data()->header(),
                    indent(2), this->taken(),
                    indent(2), this->displacement(),
                    indent(2), this->cell_count(),
                    indent());
}

void BranchData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"%s\",\n"
             "%s\"header\": %llu,\n"
             "%s\"taken\": %u,\n"
             "%s\"not_taken\": %u,\n"
             "%s\"displacement\": %d,\n"
             "%s\"cell_count\": %d\n"
             "%s}", indent(2), this->class_name(),
                    indent(2), this->data()->header(),
                    indent(2), this->taken(),
                    indent(2), this->not_taken(),
                    indent(2), this->displacement(),
                    indent(2), this->cell_count(),
                    indent());
}


void MultiBranchData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"MultiBranchData\",\n"
             "%s\"header\": %llu,\n"
             "%s\"cell_count\": %d,\n"
             "%s\"default_count\": %u,\n"
             "%s\"default_displacement\": %d,\n"
             "%s\"array\": [", indent(2),
                    indent(2), this->data()->header(),
                    indent(2), this->cell_count(),
                    indent(2), this->default_count(),
                    indent(2), this->default_displacement(),
                    indent(2)
    );

  if(this->number_of_cases() == 0) {
    fputs(" ]", f);
  } else {
    for(int i = 0; i < this->number_of_cases(); i++) {
      fprintf(f, "%s\n%s{\n"
                     "%s\"count\": %u,\n"
                     "%s\"displacement\": %d\n"
                     "%s}",
                (i == 0) ? "" : ",", indent(4),
                indent(6), this->count_at(i),
                indent(6), this->displacement_at(i),
                indent(4)
        );
    }
    fprintf(f, "\n%s]", indent(2));
  }

  fprintf(f, "\n%s}", indent());
}

void ArgInfoData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"ArgInfoData\",\n"
             "%s\"header\": %llu,\n"
             "%s\"cell_count\": %d,\n"
             "%s\"array\": [", indent(2),
                    indent(2), this->data()->header(),
                    indent(2), this->cell_count(),
                    indent(2)
    );

  if(this->number_of_args() == 0) {
    fputs(" ]", f);
  } else {
    for(int i = 0; i < this->number_of_args(); i++) {
      fprintf(f, "%s\n%s%u",
                (i == 0) ? "" : ",", indent(4), this->arg_modified(i));
    }
    fprintf(f, "\n%s]", indent(2));
  }

  fprintf(f, "\n%s}", indent());
}

void ParametersTypeData::serialize_to_file(const Indenter& indent, FILE *f) const {
  fprintf(f, "{\n"
             "%s\"type\": \"ParametersTypeData\",\n"
             "%s\"header\": %llu,\n"
             "%s\"cell_count\": %d,\n"
             "%s\"array\": [", indent(2),
                    indent(2), this->data()->header(),
                    indent(2), this->cell_count(),
                    indent(2)
    );

  if(this->number_of_parameters() == 0) {
    fputs(" ]", f);
  } else {
    for(int i = 0; i < this->number_of_parameters(); i++) {
      intptr_t val = this->parameters()->type(i);
      Klass *klass = TypeEntries::valid_klass(val);
      fprintf(f, "%s\n%s{\n"
                         "%s\"type\": \"%s\",\n"
                         "%s\"slot\": %d,\n"
                         "%s\"flags\": %d\n"
                     "%s}",
          (i == 0) ? "" : ",",
          indent(4), indent(6),
          (klass == NULL) ? "" : klass->name()->as_C_string(),
          indent(6),
          this->parameters()->stack_slot(i),
          indent(6),
          val & 3,
          indent(4)
      );
    }
    fprintf(f, "\n%s]", indent(2));
  }
  fprintf(f, "\n%s}", indent());
}

void SpeculativeTrapData::serialize_to_file(const Indenter& indent, FILE *f) const {
  if(this->method() != NULL) {
    fprintf(f, "{ \"type\": \"SpeculativeTrapData\" }");
    return;
  }

  Method* method = this->method();
  char method_name_buf[1024];
  Symbol *method_name = method->name();
  method_name->as_C_string(method_name_buf, sizeof(method_name_buf));

  char method_sig_buf[1024];
  Symbol *method_sig = method->signature();
  method_sig->as_C_string(method_sig_buf, sizeof(method_sig_buf));

  char klass_name_buf[1024];
  Symbol *klass_name = method->klass_name();
  klass_name->as_C_string(klass_name_buf, sizeof(klass_name_buf));

  const char *loader_name = method->method_holder()->class_loader_data()->loader_name();

  fprintf(f, "{\n"
             "%s\"type\": \"SpeculativeTrapData\",\n"
             "%s\"loader\": \"%s\",\n"
             "%s\"klass\": \"%s\",\n"
             "%s\"method\": \"%s\",\n"
             "%s\"sig\": \"%s\"\n"
             "%s}",
            indent(2),
            indent(2), loader_name,
            indent(2), klass_name_buf,
            indent(2), method_name_buf,
            indent(2), method_sig_buf,
            indent()
  );
}


Serializer<MethodCounters> MethodCounters::serializer() {

  static const FieldSerializer<MethodCounters> fields[] = {
#define FIELD(NAME) \
    FieldSerializer<MethodCounters>::build(#NAME, &MethodCounters::NAME),

    FIELD(_interpreter_invocation_count)
    FIELD(_interpreter_throwout_count)
    FIELD(_number_of_breakpoints)
    FIELD(_invocation_counter)
    FIELD(_backedge_counter)
    FIELD(_nmethod_age)
    //FIELD(_interpreter_invocation_limit)
    //FIELD(_interpreter_backward_branch_limit)
    //FIELD(_interpreter_profile_limit)
    FIELD(_invoke_mask)
    FIELD(_backedge_mask)
    FIELD(_rate)
    FIELD(_prev_time)
    FIELD(_highest_comp_level)
    FIELD(_highest_osr_comp_level)
  };

  Serializer<MethodCounters> sr(fields);

  if(SkipSerializedInvokeAndBackedgeCounters) {
    static const FieldSerializer<MethodCounters> skipped_counter_fields[] = {
      FIELD(_invocation_counter)
      FIELD(_backedge_counter)
    };
    sr.skip_fields(skipped_counter_fields);
  }
#undef FIELD
  return sr;
}

void MethodCounters::serialize_to_file(int indent, FILE *f) const {

  const Serializer<MethodCounters> &sr = MethodCounters::serializer();
  sr.serialize_to_file(this, indent, f);
}

MethodCounters* MethodCounters::deserialize_from_json(Method *method, const rapidjson::Value &json, TRAPS) {

  MethodCounters *c = method->method_counters() ?:
                      MethodCounters::allocate(method, THREAD);

  if(!LoadSerializedProfilingData) {
    return c;
  }

  c->deserialize_from_json(method, json);

  return c;
}

void MethodCounters::deserialize_from_json(Method *method, const rapidjson::Value &json) {

  const Serializer<MethodCounters> &sr = MethodCounters::serializer();
  sr.deserialize_from_json(this, json);

  if(ZeroLoadedInvocationAndBackedgeCounters) {
    this->invocation_counter()->init();
    this->backedge_counter()->init();
  }
}



MethodData *MethodData::deserialize_from_json(Method *method, const rapidjson::Value &json, TRAPS) {

  ClassLoaderData* loader_data = method->method_holder()->class_loader_data();
  MethodData *mdo = method->method_data() ?:
                    MethodData::allocate(loader_data, method, THREAD);

  if(!LoadSerializedProfilingData) {
    return mdo;
  }

  mdo->deserialize_from_json(json);
  return mdo;
}


void MethodData::deserialize_from_json(const rapidjson::Value &json) {

  const Serializer<MethodData> &sr = MethodData::serializer();
  Method *method = this->method();

  // Verify the serialized data still matches the method
  if(json["fields"]["_size"] != this->_size ||
     json["fields"]["_data_size"] != this->_data_size) {

    if(!QuietDeserializationWarning) {
      tty->print("Warning: Failed to deserialize method %s\n",
                 method->name_and_sig_as_C_string());
    }
    return;
  }

  sr.deserialize_from_json(this, json["fields"]);
  if(ZeroLoadedInvocationAndBackedgeCounters) {
    this->invocation_counter()->init();
    this->backedge_counter()->init();
  }

  size_t i = 0, data_size = json["data"].Size();
  const rapidjson::Value &json_data = json["data"];
  if (_parameters_type_data_di != no_parameters) {
    this->parameters_type_data()->deserialize_from_json(json_data[i]);
    i++;
  }

  ProfileData* data = this->first_data();
  for ( ; this->is_valid(data) && i < data_size; data = this->next_data(data), i++) {

    bool res = data->deserialize_from_json(json_data[i]);
    if(!res) {
      tty->print("Warning: Only partial deserialization of method %s\n",
                 method->name_and_sig_as_C_string());
      break;
    }
  }


  const rapidjson::Value &extra_data = json["extra_data"];
  DataLayout* dp    = extra_data_base();
  DataLayout* end   = args_data_limit();
  for(uint i = 0; i < extra_data.Size(); dp = next_extra(dp), i++) {
    if(dp >= end) {
      break;
    }

    int tag = dp->tag();
    data = NULL;

    if(tag == DataLayout::no_tag) {
      continue;
    } else if(tag == DataLayout::bit_data_tag) {
      data = new BitData(dp);
    } else if(tag == DataLayout::speculative_trap_data_tag) {
      data = new SpeculativeTrapData(dp);
    } else if(tag == DataLayout::arg_info_data_tag) {
      data = new ArgInfoData(dp);
    } else {
      assert(false, "Unexpected extra data tag");
    }

    if(extra_data[i].MemberCount() > 0) {
      bool res = data->deserialize_from_json(extra_data[i]);
      if(!res) {
        break;
      }
    }


    if(tag == DataLayout::arg_info_data_tag) {
      break;
    }
  }
}

#define COUNTER_MAX (RandomizeSerializedProfDataMore ? \
                        os::random() \
                        : (os::random() % 2 ? 0 : 1000000))

bool BitData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "BitData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }
  if(!CHECK_RandomizeSerializedProfData()) {
    if(json["null_seen"].GetUint()) {
      this->set_null_seen();
    } else {
      this->unset_null_seen();
    }
  } else {
    if(json["null_seen"].GetUint()) {
      this->unset_null_seen();
    } else {
      this->set_null_seen();
    }
  }
  return true;
}

bool CounterData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "CounterData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  if(CHECK_RandomizeSerializedProfData()) {
    this->set_count(COUNTER_MAX);
  } else {
    this->set_count(json["count"].GetUint());
  }
  return true;
}

Klass *lookup_klass(const char *klass_str) {
  size_t len = strlen(klass_str);
  if(len == 0) {
    return NULL;
  }

  uint hash;
  Symbol *klass_name = SymbolTable::lookup_only(klass_str, len, hash);
  if(klass_name == NULL) {
    return NULL;
  }

  Klass *klass = SystemDictionary::resolve_or_null(klass_name, Thread::current());
  if(klass == NULL) {
    klass = ClassLoaderDataGraph::lookup_klass_by_name(klass_name);
    if(klass == NULL) {
      tty->print_cr("Klass name lookup failed: %s", klass_str);
    }
  }
  return klass;
}

bool ReceiverTypeData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != this->class_name() ||
     this->cell_count() != json["cell_count"].GetInt() ||
     json["receivers"].Size() != this->row_limit() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  // XXX To blame!!!:
  if(!CHECK_RandomizeSerializedProfData()) {
    this->set_count(json["count"].GetUint());
  } else {
    this->set_count(COUNTER_MAX);
    //this->set_count(0);
  }

  const rapidjson::Value &receivers = json["receivers"];
  for(uint i = 0; i < this->row_limit(); i++) {

    Klass *klass = NULL;

    if(receivers[i].MemberCount() != 0) {
      const char *klass_str = receivers[i]["class"].GetString();
      klass = lookup_klass(klass_str);
    }

    if(klass != NULL) {
      this->set_receiver(i, klass);
      this->set_receiver_count(i, receivers[i]["count"].GetUint());
      if(CHECK_RandomizeSerializedProfData()) {
        this->set_receiver(i, NULL);
      } else if(CHECK_RandomizeSerializedProfData()) {
        this->set_receiver_count(i, COUNTER_MAX);
      }
    } else {
      this->set_receiver(i, NULL);
      this->set_receiver_count(i, 0);
    }

    // XXX ciMethod::call_profile_at_bci will complain if this->count() > 0 when
    //     there is fewer than two recorded receivers.
    for(uint i = 0; i < this->row_limit(); i++) {
      if(this->receiver(i) == NULL) {
        this->set_count(0);
        break;
      }
    }
  }

  return true;
}

bool VirtualCallData::deserialize_from_json(const rapidjson::Value &json) {
  return this->ReceiverTypeData::deserialize_from_json(json);
}

bool VirtualCallTypeData::deserialize_from_json(const rapidjson::Value &json) {

  this->ReceiverTypeData::deserialize_from_json(json);

  const rapidjson::Value &args = json["args"];
  for(int i = 0; i < this->number_of_arguments(); i++) {
    Klass *klass = lookup_klass(args[i]["type"].GetString());
    if(klass != NULL && !CHECK_RandomizeSerializedProfData()) {
      this->_args.set_type(i, (intptr_t)klass | args[i]["flags"].GetUint());
    } else {
      this->_args.set_type(i, 0);
    }
    if(!CHECK_RandomizeSerializedProfData()) {
      this->_args.set_stack_slot(i, args[i]["slot"].GetUint());
    } else {
      this->_args.set_stack_slot(i, 0);
    }
  }

  if(this->has_return()) {
    const rapidjson::Value &ret = json["return"];
    Klass *klass = lookup_klass(ret["type"].GetString());
    if(klass != NULL && !CHECK_RandomizeSerializedProfData()) {
      this->_ret.set_type((intptr_t)klass | ret["flags"].GetUint());
    } else {
      // TODO: Should I preserve the "flags"?
      this->_ret.set_type(0);
    }
  }
  return true;
}

bool RetData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "RetData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     json["items"].Size() != this->row_limit() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  this->set_count(json["count"].GetUint());

  const rapidjson::Value &items = json["items"];
  for(uint i = 0; i < this->row_limit(); i++) {
    this->set_bci(i, items[i]["bci"].GetInt());
    if(!CHECK_RandomizeSerializedProfData()) {
      this->set_bci_count(i, items[i]["bci_count"].GetUint());
    } else {
      this->set_bci_count(i, COUNTER_MAX);
    }
    this->set_bci_displacement(i, items[i]["bci_displacement"].GetInt());
  }
  return true;
}

bool CallTypeData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "CallTypeData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     json["args"].Size() != (uint)this->number_of_arguments() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  if(!CHECK_RandomizeSerializedProfData()) {
    this->set_count(json["count"].GetUint());
  } else {
    this->set_count(COUNTER_MAX);
  }

  const rapidjson::Value &args = json["args"];
  for(int i = 0; i < this->number_of_arguments(); i++) {
    Klass *klass = lookup_klass(args[i]["type"].GetString());
    if(klass != NULL && !CHECK_RandomizeSerializedProfData()) {
      this->_args.set_type(i, (intptr_t)klass | args[i]["flags"].GetUint());
    } else {
      // TODO: Preserve flags?
      this->_args.set_type(i, 0);
    }
    if(!CHECK_RandomizeSerializedProfData()) {
      this->_args.set_stack_slot(i, args[i]["slot"].GetUint());
    } else {
      this->_args.set_stack_slot(i, 0);
    }
  }

  if(this->has_return()) {
    const rapidjson::Value &ret = json["return"];
    Klass *klass = lookup_klass(ret["type"].GetString());
    if(klass != NULL && !CHECK_RandomizeSerializedProfData()) {
      this->_ret.set_type((intptr_t)klass | ret["flags"].GetUint());
    } else {
      this->_ret.set_type(0);
    }
  }
  return true;
}

bool JumpData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "JumpData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  if(!CHECK_RandomizeSerializedProfData()) {
    this->set_taken(json["taken"].GetUint());
  } else {
    this->set_taken(COUNTER_MAX);
  }
  //this->set_displacement(json["displacement"].GetInt());
  assert(this->displacement() == json["displacement"].GetInt(), "");
  return true;
}

#ifdef DEBUG
const rapidjson::Value &json_member(const rapidjson::Value &json, const char *n) {
  return json[n];
}
#endif

bool BranchData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "BranchData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  if(!CHECK_RandomizeSerializedProfData()) {
    this->set_taken(json["taken"].GetUint());
  } else {
    this->set_taken(COUNTER_MAX);
  }
  if(!CHECK_RandomizeSerializedProfData()) {
    this->set_not_taken(json["not_taken"].GetUint());
  } else {
    this->set_not_taken(COUNTER_MAX);
  }
  assert(this->displacement() == json["displacement"].GetInt(), "");
  return true;
}

bool MultiBranchData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "MultiBranchData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     (uint)this->number_of_cases() != json["array"].Size() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  if(!CHECK_RandomizeSerializedProfData()) {
    this->set_default_count(json["default_count"].GetUint());
  } else {
    this->set_default_count(COUNTER_MAX);
  }
  this->set_default_displacement(json["default_displacement"].GetInt());

  const rapidjson::Value &array = json["array"];
  for(int i = 0; i < this->number_of_cases(); i++) {
    if(!CHECK_RandomizeSerializedProfData()) {
      this->set_count_at(i, array[i]["count"].GetInt());
    } else {
      this->set_count_at(i, COUNTER_MAX);
    }
    assert(this->displacement_at(i) == array[i]["displacement"].GetInt(), "");
  }
  return true;
}

bool ArgInfoData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "ArgInfoData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     (uint)this->number_of_args() != json["array"].Size() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  const rapidjson::Value &array = json["array"];
  for(int i = 0; i < this->number_of_args(); i++) {
    if(!CHECK_RandomizeSerializedProfData()) {
      this->set_arg_modified(i, array[i].GetUint());
    } else {
      if(array[i].GetUint()) {
        this->set_arg_modified(i, -1);
      } else {
        this->set_arg_modified(i, 0);
      }
    }
  }

  return true;
}

bool ParametersTypeData::deserialize_from_json(const rapidjson::Value &json) {
  if(json["type"] != "ParametersTypeData" ||
     this->cell_count() != json["cell_count"].GetInt() ||
     (uint)this->number_of_parameters() != json["array"].Size() ||
     !this->data()->load_serialized_header(json["header"].GetInt64())) {
    return false;
  }

  const rapidjson::Value &array = json["array"];
  for(int i = 0; i < this->number_of_parameters(); i++) {
    const rapidjson::Value &item = array[i];
    if(!CHECK_RandomizeSerializedProfData()) {
        this->_parameters.set_stack_slot(i, item["slot"].GetUint());
    } else {
        this->_parameters.set_stack_slot(i, 0);
    }

    Klass *klass = lookup_klass(item["type"].GetString());
    if(klass == NULL || CHECK_RandomizeSerializedProfData()) {
      this->_parameters.set_type(i, 0);
    } else {
      this->_parameters.set_type(i, (intptr_t)klass | item["flags"].GetUint());
    }
  }

  return true;
}

bool SpeculativeTrapData::deserialize_from_json(const rapidjson::Value &json) {
  guarantee(false, "Not implemented");
  tty->print_raw_cr("Warning: Deserialization of SpeculativeTrapData isn't implemented (TODO)");
  // TODO!
  return true;
}

