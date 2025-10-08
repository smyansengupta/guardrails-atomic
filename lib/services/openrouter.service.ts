import { CodeGenerationError } from '@/lib/utils/errors';

/**
 * Generate code using OpenRouter API
 *
 * @param prompt - The prompt to send to the LLM
 * @param model - The model to use (default: gpt-4)
 * @returns The generated response
 */
export async function generateWithOpenRouter(
  prompt: string,
  model: string = 'openai/gpt-4'
): Promise<string> {
  try {
    // Support both OPENROUTER_API_KEY (preferred) and OPENAI_API_KEY (fallback)
    const apiKey = process.env.OPENROUTER_API_KEY || process.env.OPENAI_API_KEY;

    if (!apiKey) {
      throw new CodeGenerationError('Missing API key: Set OPENROUTER_API_KEY or OPENAI_API_KEY in .env.local');
    }

    const response = await fetch("https://openrouter.ai/api/v1/chat/completions", {
      method: "POST",
      headers: {
        "Authorization": `Bearer ${apiKey}`,
        "HTTP-Referer": `${process.env.PROJECT_URL || 'http://localhost:3000'}`,
        "X-Title": `${process.env.PROJECT_NAME || 'Guardrails: Atomic'}`,
        "Content-Type": "application/json"
      },
      body: JSON.stringify({
        "model": model,
        "messages": [
          { "role": "user", "content": prompt }
        ]
      })
    });

    if (!response.ok) {
      throw new Error(`OpenRouter API request failed with status ${response.status}`);
    }

    const data = await response.json();
    return data.choices[0].message.content;
  } catch (error) {
    throw new CodeGenerationError(`Failed to generate code with OpenRouter: ${error}`);
  }
}