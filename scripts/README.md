# Manual Integration Tests

This directory contains manual integration tests that use real external services (LLM APIs, Docker, etc.).

⚠️ **DO NOT** run these in automated CI/CD - they cost money and require external dependencies!

## Code Generator Test

Tests the code generator with real OpenRouter API calls.

### Prerequisites

1. Create a `.env.local` file in the project root:
   ```bash
   OPENAI_API_KEY=sk-or-v1-your-openrouter-key-here
   PROJECT_URL=http://localhost:3000
   PROJECT_NAME=Guardrails
   ```

2. Get an OpenRouter API key from https://openrouter.ai/

### Run the Test

```bash
pnpm tsx scripts/test-code-generator.ts
```

### What It Tests

1. ✅ Loads the transfer spec from `templates/specs/transfer.yaml`
2. ✅ Generates initial TypeScript code using OpenRouter
3. ✅ Validates the generated code structure
4. ✅ Simulates repair mode with mock feedback
5. ✅ Generates repaired code that addresses the violation

### Expected Output

The test should:
- Generate valid TypeScript code
- Include proper function signatures
- Handle idempotency (in repair mode)
- Take 10-20 seconds total (due to LLM API calls)

### Troubleshooting

**Error: "Missing API key"**
- Make sure `OPENAI_API_KEY` is set in `.env.local`
- Verify the key starts with `sk-or-v1-`

**Error: "Template not found"**
- Run from the project root directory
- Check that `templates/prompts/` exists

**LLM returns invalid code**
- This can happen occasionally with GPT-4
- Try running the test again
- Check the OpenRouter dashboard for errors
