# Implementation Plan: Input Provider Refactoring

Date: 2025-08-05

## Selected Approach

Refactor the interactive input system to use an abstraction layer that enables proper testing while maintaining all current functionality. This approach was selected (Option 3 from analysis) because it:
- Fixes the root cause of test failures (unmockable input() calls)
- Creates a cleaner, more testable architecture
- Maintains all existing functionality
- Follows the project's design philosophy of explicit interfaces and fail-fast principles

## Test-Driven Development Strategy

- **Test categories**: Unit tests for input provider, integration tests for interactive components
- **Testing framework**: Following project's pytest standards from Tests Guide
- **Success criteria**: All existing tests pass with proper mocking, no direct input() calls in tests

## Implementation Phases

### Phase 1: Create Input Provider Abstraction (Priority: High)

**Objective**: Create a clean abstraction for user input that can be easily mocked in tests

**Tests to Write First**:
- `test_input_provider.py`: Test the input provider interface and implementations
- `test_console_input_provider.py`: Test the real console implementation
- `test_mock_input_provider.py`: Test the mock implementation for testing

**Implementation Tasks**:
1. Create `InputProvider` base class with clear interface
2. Implement `ConsoleInputProvider` for production use
3. Implement `MockInputProvider` for testing
4. Add factory function for creating appropriate provider

**Success Criteria**:
- [ ] Input provider interface is clean and minimal
- [ ] Console provider works identically to current input() calls
- [ ] Mock provider enables deterministic testing
- [ ] All providers follow project's no-decorator policy

### Phase 2: Refactor InteractiveSaveManager (Priority: High)

**Objective**: Update InteractiveSaveManager to use InputProvider instead of direct input() calls

**Tests to Write First**:
- Update `test_interactive.py` to use MockInputProvider
- Ensure all existing test cases still validate the same behavior
- Add tests for edge cases (empty input, special characters)

**Implementation Tasks**:
1. Add InputProvider as REQUIRED parameter to InteractiveSaveManager.__init__()
2. Replace input() call in prompt_save_mode() with provider.get_input()
3. Find and update ALL instantiations to pass appropriate provider
4. Remove any code that worked without a provider

**Success Criteria**:
- [ ] All interactive tests pass without OSError
- [ ] No direct input() calls remain in InteractiveSaveManager
- [ ] ALL call sites updated with explicit provider
- [ ] Tests properly mock all user interactions

### Phase 3: Update BuildModule Integration (Priority: High)

**Objective**: Update BuildModule and ALL related components to use the new input system

**Tests to Write First**:
- Update all failing tests in `test_build_module_interactive.py`
- Update `test_cli_interactive_integration.py`
- Add test to verify no components create InteractiveSaveManager without provider

**Implementation Tasks**:
1. Update BuildModule to create appropriate InputProvider
2. Pass provider to InteractiveSaveManager during initialization
3. Find and update EVERY component that creates InteractiveSaveManager
4. Ensure CLI properly initializes the console provider
5. Remove any fallback code or optional parameter handling

**Success Criteria**:
- [ ] All builder component tests pass
- [ ] CLI integration tests pass
- [ ] ZERO instances of InteractiveSaveManager created without provider
- [ ] Clean, mandatory dependency injection pattern

### Phase 4: Fix Output Integration Tests (Priority: Medium)

**Objective**: Update output integration tests to match current simplified formatter behavior

**Tests to Write First**:
- Review actual output from MarkdownFormatter
- Update test expectations to match current implementation

**Implementation Tasks**:
1. Update test expectations in `test_output_integration.py`
2. Remove expectations for structured markdown headers
3. Adjust assertions to match simplified output format
4. Document the design decision in test comments

**Success Criteria**:
- [ ] All output integration tests pass
- [ ] Tests accurately reflect current formatter behavior
- [ ] Test comments explain the simplified output design
- [ ] No changes to production code needed

### Phase 5: Documentation and Cleanup (Priority: Low)

**Objective**: Update documentation and perform final cleanup

**Implementation Tasks**:
1. Update output/README.md to document InputProvider pattern
2. Add examples of proper testing with MockInputProvider
3. Update any affected component documentation
4. Clean up any temporary debugging code

**Success Criteria**:
- [ ] Documentation reflects new architecture
- [ ] Testing patterns clearly documented
- [ ] All temporary code removed
- [ ] Style Guide compliance verified

## Risk Mitigation

1. **All Call Sites Must Be Updated**: Every place that creates InteractiveSaveManager needs updating
   - Mitigation: Use grep to find all instantiations and update them systematically
   - This is intentional - we want a clean, unified interface

2. **Test Complexity**: New abstraction might make tests more complex
   - Mitigation: Provide clear test utilities and examples

3. **Performance**: Additional abstraction layer might impact performance
   - Mitigation: Keep abstraction minimal, no complex logic

## Timeline Estimate

- Phase 1: 2-3 hours (create clean abstraction)
- Phase 2: 2-3 hours (refactor and test InteractiveSaveManager)
- Phase 3: 2-3 hours (update all integrations)
- Phase 4: 1-2 hours (fix test expectations)
- Phase 5: 1 hour (documentation)

Total: 8-12 hours of focused development

## Dependencies

- No external dependencies required
- Uses existing pytest testing framework
- Compatible with current Python version

## Notes

- This refactoring follows the project's "fail fast" philosophy by making dependencies explicit
- The abstraction is minimal and focused solely on testability
- No decorators or complex patterns, following project standards
- The solution respects the apparent design decision to simplify markdown output