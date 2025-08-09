"""Tests for bitvector operation utilities."""

import pytest
import z3

# Import from utils
from model_checker.utils.bitvector import (
    binary_bitvector, int_to_binary, index_to_substate,
    bitvec_to_substates, bitvec_to_worldstate
)


class TestBinaryBitvector:
    """Test binary_bitvector function."""
    
    def test_binary_bitvector_mod4(self):
        """Test with bit width that is multiple of 4."""
        bit = z3.BitVecVal(0x0F, 8)
        result = binary_bitvector(bit, 8)
        assert result == '#b00001111'
    
    def test_binary_bitvector_not_mod4(self):
        """Test with bit width that is not multiple of 4."""
        bit = z3.BitVecVal(7, 3)
        result = binary_bitvector(bit, 3)
        assert result == '#b111'  # Returns raw sexpr for N % 4 != 0


class TestIntToBinary:
    """Test int_to_binary function."""
    
    def test_basic_conversion(self):
        assert int_to_binary(15, 8) == '#b00001111'
        assert int_to_binary(255, 8) == '#b11111111'
        assert int_to_binary(0, 4) == '#b0000'
    
    def test_padding(self):
        assert int_to_binary(1, 8) == '#b00000001'
        assert int_to_binary(1, 16) == '#b0000000000000001'


class TestIndexToSubstate:
    """Test index_to_substate function."""
    
    def test_single_letters(self):
        assert index_to_substate(0) == 'a'
        assert index_to_substate(1) == 'b'
        assert index_to_substate(24) == 'y'  # Single 'y'
    
    def test_double_letters(self):
        assert index_to_substate(25) == 'zz'  # 25 maps to double 'z'
        assert index_to_substate(26) == 'aa'
        assert index_to_substate(27) == 'bb'
        assert index_to_substate(51) == 'zzz'
    
    def test_multiple_letters(self):
        assert index_to_substate(52) == 'aaa'
        assert index_to_substate(194) == 'mmmmmmmm'


class TestBitvecToSubstates:
    """Test bitvec_to_substates function."""
    
    def test_null_state(self):
        """Test conversion of zero bitvector."""
        bit = z3.BitVecVal(0, 3)
        assert bitvec_to_substates(bit, 3) == "□"
    
    def test_single_state(self):
        """Test conversion with single bit set."""
        bit = z3.BitVecVal(1, 3)  # 001
        assert bitvec_to_substates(bit, 3) == "a"
        
        bit = z3.BitVecVal(2, 3)  # 010
        assert bitvec_to_substates(bit, 3) == "b"
        
        bit = z3.BitVecVal(4, 3)  # 100
        assert bitvec_to_substates(bit, 3) == "c"
    
    def test_fusion_state(self):
        """Test conversion with multiple bits set."""
        bit = z3.BitVecVal(3, 3)  # 011
        assert bitvec_to_substates(bit, 3) == "a.b"
        
        bit = z3.BitVecVal(7, 3)  # 111
        assert bitvec_to_substates(bit, 3) == "a.b.c"
    
    def test_integer_input(self):
        """Test handling of integer inputs."""
        assert bitvec_to_substates(5, 3) == "a.c"
    
    def test_invalid_input(self):
        """Test handling of invalid inputs."""
        result = bitvec_to_substates("invalid", 3)
        assert result.startswith("<unknown-")


class TestBitvecToWorldstate:
    """Test bitvec_to_worldstate function."""
    
    def test_single_letters(self):
        """Test mapping to single letters."""
        assert bitvec_to_worldstate(z3.BitVecVal(0, 8)) == 'a'
        assert bitvec_to_worldstate(z3.BitVecVal(1, 8)) == 'b'
        assert bitvec_to_worldstate(z3.BitVecVal(25, 8)) == 'z'
    
    def test_double_letters(self):
        """Test mapping to double letters."""
        assert bitvec_to_worldstate(z3.BitVecVal(26, 8)) == 'aa'
        assert bitvec_to_worldstate(z3.BitVecVal(27, 8)) == 'bb'
        assert bitvec_to_worldstate(z3.BitVecVal(51, 8)) == 'zz'
    
    def test_integer_input(self):
        """Test with integer inputs."""
        assert bitvec_to_worldstate(0) == 'a'
        assert bitvec_to_worldstate(26) == 'aa'
    
    def test_invalid_input(self):
        """Test handling of invalid inputs."""
        result = bitvec_to_worldstate("invalid")
        assert result.startswith("<unknown-")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])