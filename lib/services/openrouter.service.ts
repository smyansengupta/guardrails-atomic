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
    const response = await fetch("https://openrouter.ai/api/v1/chat/completions", {
      method: "POST",
      headers: {
        "Authorization": `Bearer ${process.env.OPENAI_API_KEY}`,
        "HTTP-Referer": `${process.env.PROJECT_URL}`,
        "X-Title": `${process.env.PROJECT_NAME}`,
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