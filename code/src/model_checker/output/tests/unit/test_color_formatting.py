"""Tests for ANSI color conversion to markdown."""

import pytest

from model_checker.output.formatters import ANSIToMarkdown


class TestColorFormatting:
    """Test ANSI escape code conversion."""
    
    def setup_method(self):
        """Create converter instance."""
        self.converter = ANSIToMarkdown()
        
    def test_convert_red_text(self):
        """Test red ANSI code conversion."""
        ansi_text = "\033[31mRED TEXT\033[0m"
        result = self.converter.convert(ansi_text)
        assert result == "**RED TEXT**"  # Red becomes bold
        
    def test_convert_green_text(self):
        """Test green ANSI code conversion."""
        ansi_text = "\033[32mGREEN TEXT\033[0m"
        result = self.converter.convert(ansi_text)
        assert result == "_GREEN TEXT_"  # Green becomes italic
        
    def test_convert_mixed_colors(self):
        """Test mixed color conversion."""
        ansi_text = "Normal \033[31mRED\033[0m and \033[32mGREEN\033[0m text"
        result = self.converter.convert(ansi_text)
        assert result == "Normal **RED** and _GREEN_ text"
        
    def test_preserve_non_colored_text(self):
        """Test that non-colored text is preserved."""
        ansi_text = "This has no colors"
        result = self.converter.convert(ansi_text)
        assert result == "This has no colors"
        
    def test_handle_nested_formatting(self):
        """Test handling of nested or complex formatting."""
        # Test with reset in middle
        ansi_text = "\033[31mRED \033[0mNORMAL \033[32mGREEN\033[0m"
        result = self.converter.convert(ansi_text)
        assert result == "**RED **NORMAL _GREEN_"
        
    def test_strip_unsupported_codes(self):
        """Test stripping of unsupported ANSI codes."""
        # Test with various ANSI codes
        ansi_text = "\033[1mBOLD\033[0m \033[4mUNDERLINE\033[0m"
        result = self.converter.convert(ansi_text)
        # Should strip unsupported codes but preserve text
        assert "BOLD" in result
        assert "UNDERLINE" in result
        assert "\033" not in result
        
    def test_handle_color_codes_at_boundaries(self):
        """Test color codes at string boundaries."""
        # Color at start
        ansi_text = "\033[31mSTART"
        result = self.converter.convert(ansi_text)
        assert result == "**START**"
        
        # Color at end
        ansi_text = "END\033[0m"
        result = self.converter.convert(ansi_text)
        assert "\033" not in result
        
    def test_convert_state_indicators(self):
        """Test conversion preserves state type indicators."""
        # Simulate colored state output
        ansi_text = "States: \033[32ms0\033[0m (possible), \033[31ms1\033[0m (impossible)"
        result = self.converter.convert(ansi_text)
        assert "_s0_" in result  # Green -> italic
        assert "**s1**" in result  # Red -> bold
        assert "(possible)" in result
        assert "(impossible)" in result